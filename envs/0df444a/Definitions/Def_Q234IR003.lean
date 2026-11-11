-- Prove2me | Definitions.Def_Q234IR003
-- name    : Q234IR003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:36.646277+00:00
-- url     : https://prove2.me/theorems/e1ad94bb-ffdc-4c6b-a8d9-323c8ace269a
-- title:
--   Definitions bundle Q234IR003 of the split of OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Invariant233.Results.prescribed_irrational_counterexample` and `OAI.Invariant233.Results.product_realization`, carved from OpenAI's openai/math development (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 287 declarations of OpenAI's Lean: 120 definitions, 5 inductive types or structures, 15 instances and 147 theorems. The definitions and types are `OAI.Invariant233.CircleParameterLaws.blocksWithZero`, `OAI.Invariant233.CircleParameterLaws.budgetBlocks`, `OAI.Invariant233.CircleParameterRecursion.Step`, `OAI.Invariant233.CircleParameterRecursion.choices`, `OAI.Invariant233.CircleParameterRecursion.chooseStep`, `OAI.Invariant233.CircleParameterRecursion.constructed`, `OAI.Invariant233.CircleParameterRecursion.globalFrequency`, `OAI.Invariant233.CircleParameterRecursion.nextState`, `OAI.Invariant233.CircleParameterRecursion.states`, `OAI.Invariant233.ConcretePredual.completedPredualNormedSpace`, `OAI.Invariant233.ConcretePredual.evaluationLinearIsometryEquiv`, `OAI.Invariant233.DiagonalGauge.conjugate`, `OAI.Invariant233.DiagonalGauge.coordinate`, `OAI.Invariant233.DiagonalGauge.fieldOperator`, `OAI.Invariant233.DiagonalGauge.fourierOperator`, `OAI.Invariant233.DiagonalGauge.inclusion`, `OAI.Invariant233.Fejer.approximation`, `OAI.Invariant233.Fejer.approximationCoefficient`, `OAI.Invariant233.Fejer.bundledKernel`, `OAI.Invariant233.Fejer.coefficient`, `OAI.Invariant233.Fejer.geometricPolynomial`, `OAI.Invariant233.Fejer.kernel`, `OAI.Invariant233.FiniteKernelMixture.diagonalReplacementKernel`, `OAI.Invariant233.IsFaithfulTracialVector.toTracialState`, `OAI.Invariant233.MixedRadix.Nonterminal`, `OAI.Invariant233.MixedRadix.canonicalDigits`, `OAI.Invariant233.MixedRadix.circleCanonical`, `OAI.Invariant233.MixedRadix.digitLaw`, `OAI.Invariant233.MixedRadix.extendPrefix`, `OAI.Invariant233.MixedRadix.finitePrefixRankEquiv`, `OAI.Invariant233.MixedRadix.tailValue`, `OAI.Invariant233.OneCoordinateCoupling.leftGivenRight`, `OAI.Invariant233.OneCoordinateCoupling.leftMarginalDensity`, `OAI.Invariant233.OneCoordinateCoupling.pairLaw`, `OAI.Invariant233.OneCoordinateCoupling.replacementDensity`, `OAI.Invariant233.OneCoordinateCoupling.rightGivenLeft`, `OAI.Invariant233.OneCoordinateCoupling.rightMarginalDensity`, `OAI.Invariant233.OneCoordinateCoupling.triangleLaw`, `OAI.Invariant233.OrbitInvariance.shiftMap`, `OAI.Invariant233.OrbitInvariance.shiftUnit` and 85 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `IrrationalRotation_Analysis_ConcretePredualComplete`, `IrrationalRotation_Analysis_ConcretePredualRepresentation`, `IrrationalRotation_Analysis_ContinuityCoboundary`, `IrrationalRotation_Analysis_FejerApproximation`, `IrrationalRotation_Analysis_FejerKernel`, `IrrationalRotation_Analysis_FieldMultiplierAdjoint`, `IrrationalRotation_Analysis_FieldMultiplierCutoff`, `IrrationalRotation_Analysis_FiniteKernelMixture`, `IrrationalRotation_Analysis_LaurentNoncancellation`, `IrrationalRotation_Analysis_LaurentWindow`, `IrrationalRotation_Analysis_StrongFourierRecovery`, `IrrationalRotation_Analysis_TriangularSecondMarginal`, `IrrationalRotation_Couplings_OneCoordinateCoupling`, `IrrationalRotation_Couplings_PrefixHybrid`, `IrrationalRotation_Couplings_ProductConditionalData`, `IrrationalRotation_Couplings_ProductCoupling`, `IrrationalRotation_Couplings_ProductCouplingCircle`, `IrrationalRotation_Couplings_ProductSourceConditionalData`, `IrrationalRotation_Model_BlockProductCoupling`, `IrrationalRotation_Model_CompactTransfer`, `IrrationalRotation_Model_DiagonalGauge`, `IrrationalRotation_Model_Fejer`, `IrrationalRotation_Model_FejerApproximation`, `IrrationalRotation_Model_FiniteKernelMixture`, `IrrationalRotation_Model_MixedRadix`, `IrrationalRotation_Model_MixedRadixCircle`, `IrrationalRotation_Model_MixedRadixProbability`, `IrrationalRotation_Model_OneCoordinateConditional`, `IrrationalRotation_Model_OneCoordinateCoupling`, `IrrationalRotation_Model_PrefixDomination`, `IrrationalRotation_Model_ProductCocycle`, `IrrationalRotation_Model_ProductCoupling`, `IrrationalRotation_Model_ProductCouplingCircle`, `IrrationalRotation_Model_ProductPairIdentity`, `IrrationalRotation_Model_ProductPrefixDomination`, `IrrationalRotation_Model_ProductScaleSampling`, `IrrationalRotation_Model_ProductScales`, `IrrationalRotation_Model_RealTriangularLaw`, `IrrationalRotation_Model_SamplingTests`, `IrrationalRotation_Model_SawtoothSmoothing`, `IrrationalRotation_Model_SourceCouplingMarginals`, `IrrationalRotation_Model_SourceProductTail`, `IrrationalRotation_Model_StrictPhase`, `IrrationalRotation_Model_TrialSampling`, `IrrationalRotation_Model_VectorTraceState`, `IrrationalRotation_Operators_VectorTraceState`, `IrrationalRotation_PrescribedAngleConditional`, `IrrationalRotation_Product_ProductCocycle`, `IrrationalRotation_Product_ProductCovariance`, `IrrationalRotation_Product_ProductDiffuse`, `IrrationalRotation_Product_ProductFieldDiagonals`, `IrrationalRotation_Product_ProductFields`, `IrrationalRotation_Product_ProductGaugeFourier`, `IrrationalRotation_Product_ProductMultiplierFunctionalCalculus`, `IrrationalRotation_Product_ProductOrbitPair`, `IrrationalRotation_Product_ProductPairTransfer`, `IrrationalRotation_Product_ProductScaleCocycleWindow`, `IrrationalRotation_Product_ProductScaleConsequences`, `IrrationalRotation_Product_ProductScaleConstruction`, `IrrationalRotation_Product_ProductTracialInputs`, `IrrationalRotation_Product_ProductTracialVector`, `IrrationalRotation_Product_ProductWeightBridge`, `IrrationalRotation_Rotation_CircleMarginalBudget`, `IrrationalRotation_Rotation_CircleParameterRecursion`, `IrrationalRotation_Rotation_DiagonalGauge`, `IrrationalRotation_Rotation_FieldDiagonal`, `IrrationalRotation_Rotation_FieldDiagonalConvergence`, `IrrationalRotation_Rotation_FieldKoopmanDiagonal`, `IrrationalRotation_Rotation_GaugeFourierDiagonal`, `IrrationalRotation_Rotation_Rotation`, `IrrationalRotation_Rotation_RotationMeasurable`, `IrrationalRotation_Rotation_RotationTransfer`, `IrrationalRotation_Rotation_RotationTransferIntertwining`, `IrrationalRotation_Rotation_WeightedOrbitInvariance`, `IrrationalRotation_Rotation_WeightedShiftAlgebra`, `IrrationalRotation_Sampling_CirclePhaseSummability`, `IrrationalRotation_Sampling_MixedRadix`, `IrrationalRotation_Sampling_MixedRadixLaw`, `IrrationalRotation_Sampling_PrefixDomination`, `IrrationalRotation_Sampling_PrefixReferenceIdentification`, `IrrationalRotation_Sampling_ProductIdealSamplingLimit`, `IrrationalRotation_Sampling_ProductIdealSamplingProduct`, `IrrationalRotation_Sampling_ProductPrefixDomination`, `IrrationalRotation_Sampling_ProductSampling`, `IrrationalRotation_Sampling_ProductSamplingTestAlmostSure`, `IrrationalRotation_Sampling_SamplingTestTrialBridge`, `IrrationalRotation_Spectral_FieldDiagonalPolar`, `IrrationalRotation_Spectral_FieldResolvent`, `IrrationalRotation_Spectral_ProductDeterminant`, `IrrationalRotation_Spectral_ProductFinitePolar`, `IrrationalRotation_Spectral_RotationResolvent`, `IrrationalRotation_Spectral_WeightedShiftPolar`.
--
--   **Imports.** It imports the published bundle `Def_IrrationalRotation`; the bundles `Q234IR000`, `Q234IR001` and `Q234IR002` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.Invariant233.BlockedProductCoupling.ae_flatSourceEvent_coefficient_properties`, `OAI.Invariant233.BlockedProductCoupling.eventually_flatSourceEvent_mass`, `OAI.Invariant233.CircleCoupling.orderedCouplingIdentities_of_rational`, `OAI.Invariant233.OrderedProductCoupling.source_circlePairLaw_pairIdentity_of_triangular`, `OAI.Invariant233.ProductModel.SamplingWeights.ae_all_sourceCylinder_energy_tendsto_zero`, `OAI.Invariant233.ProductModel.SamplingWeights.ae_all_source_univ_energy_tendsto_zero`, `OAI.Invariant233.ProductModel.SamplingWeights.source_hasUniformL2Marginals_of_energy_convergence`, `OAI.Invariant233.ProductModel.eventually_actualSource_conditionalData`, `OAI.Invariant233.ProductModel.exists_covariantProjectionField_pairIdentity`, `OAI.Invariant233.ProductModel.hasOnlyTrivialInvariantProjections_of_sampling_and_phases`, `OAI.Invariant233.ProductModel.product_realization_of_ae_sampling`, `OAI.Invariant233.ProductSamplingPhaseMoments.expected_average_error_le_source_scale`, `OAI.Invariant233.ProductScaleLaws.eventually_source_product_tail_estimate`, `OAI.Invariant233.TrialSampling.coordinateSample_offdiag_error` and `OAI.Invariant233.TrialSampling.expectation_squaredError_le_actual_bound`; the proofs of `OAI.Invariant233.BlockedProductCoupling.ae_flatSourceEvent_coefficient_properties`, `OAI.Invariant233.BlockedProductCoupling.eventually_flatSourceEvent_mass`, `OAI.Invariant233.CircleCoupling.actual_tail_attenuation_of_ac_order`, `OAI.Invariant233.CircleCoupling.ae_endpoint_ratio_cap`, `OAI.Invariant233.CircleCoupling.ae_hybridPairLaw_ratio_cap`, `OAI.Invariant233.CircleCoupling.endpoint_absolutelyContinuous`, `OAI.Invariant233.CircleCoupling.orderedCouplingIdentities_of_rational`, `OAI.Invariant233.CircleCoupling.tail_exceptional_families_of_subset`, `OAI.Invariant233.CircleCoupling.tendsto_centralBadEvent_mass`, `OAI.Invariant233.CircleParameterLaws.exists_rational_graph_field`, `OAI.Invariant233.CircleParameterLaws.exists_rational_graph_field_with_truncation_mass`, `OAI.Invariant233.CircleParameterLaws.measurableOperator_hasOnlyTrivialInvariantProjections`, `OAI.Invariant233.OrderedProductCoupling.source_circlePairLaw_pairIdentity_of_triangular`, `OAI.Invariant233.ProductModel.SamplingWeights.ae_all_sourceCylinder_energy_tendsto_zero`, `OAI.Invariant233.ProductModel.SamplingWeights.ae_all_source_univ_energy_tendsto_zero`, `OAI.Invariant233.ProductModel.SamplingWeights.source_hasUniformL2Marginals_of_energy_convergence`, `OAI.Invariant233.ProductModel.eventually_actualSource_conditionalData`, `OAI.Invariant233.ProductModel.exists_covariantProjectionField_pairIdentity`, `OAI.Invariant233.ProductModel.factor_complete`, `OAI.Invariant233.ProductModel.factor_isTypeII1FactorWithVector`, `OAI.Invariant233.ProductModel.hasOnlyTrivialInvariantProjections_of_sampling_and_phases`, `OAI.Invariant233.ProductModel.productPolarStructure_of_admissible`, `OAI.Invariant233.ProductModel.productPolarStructure_of_weightOrbitDiffuse`, `OAI.Invariant233.ProductModel.product_realization_of_ae_sampling`, `OAI.Invariant233.ProductModel.weightedOperator_isVectorBrownMeasure_dirac_zero_of_logIntegral`, `OAI.Invariant233.ProductSamplingPhaseMoments.expected_average_error_le_source_scale`, `OAI.Invariant233.ProductScaleLaws.eventually_source_product_tail_estimate`, `OAI.Invariant233.Results.prescribed_irrational_counterexample`, `OAI.Invariant233.Results.product_realization`, `OAI.Invariant233.Rotation.exponentialTransfer_projection_transport`, `OAI.Invariant233.TrialSampling.coordinateSample_offdiag_error`, `OAI.Invariant233.TrialSampling.expectation_squaredError_le_actual_bound` and `OAI.Invariant233.exists_circle_parameters`.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
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
import Mathlib.Analysis.Fourier.AddCircleMulti
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
import Mathlib.Analysis.Normed.Module.DoubleDual
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
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.Option
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Find
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.Dynamics.Ergodic.AddCircle
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Logic.Function.Iterate
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalLExpectation
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
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
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Regular
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
import Mathlib.Probability.Distributions.Uniform
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
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Sequences
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR000
import Definitions.Def_Q234IR001
import Definitions.Def_Q234IR002

section
-- module Solutions.Q234_IR.Compat
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_VectorTraceState
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.ConcretePredual.evaluationLinearIsometry_apply _root_.OAI.Invariant233.ConcretePredual.evaluation_apply _root_.OAI.Invariant233.ConcretePredual.evaluation_vector _root_.OAI.Invariant233.ConcretePredual.inner_representingOperator _root_.OAI.Invariant233.ConcretePredual.norm_evaluation _root_.OAI.Invariant233.ConcretePredual.vectorFunctional_add_left _root_.OAI.Invariant233.ConcretePredual.vectorFunctional_add_right _root_.OAI.Invariant233.ConcretePredual.vectorFunctional_apply _root_.OAI.Invariant233.ConcretePredual.vectorFunctional_smul_left _root_.OAI.Invariant233.ConcretePredual.vectorFunctional_smul_right _root_.OAI.Invariant233.ConcretePredual.vector_coe _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProjectionMeetTrace.vectorFunctional_apply _root_.OAI.Invariant233.vectorTraceCLM_apply _root_.OAI.Invariant233.vectorTraceContinuousLinearMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vonNeumannVectorTraceCLM (M : VonNeumannAlgebra H) (ξ : H) : M →L[ℂ] ℂ :=
  (vectorTraceCLM ξ).comp M.toSubalgebra.toSubmodule.subtypeL

def IsFaithfulTracialVector.toTracialState {M : VonNeumannAlgebra H} {ξ : H}
    (h : IsFaithfulTracialVector M ξ) : TracialState M where
  toContinuousLinearMap := vonNeumannVectorTraceCLM M ξ
  map_one := by
    change inner ℂ ξ ξ = 1
    rw [inner_self_eq_norm_sq_to_K, h.1]
    norm_num
  map_star := by
    intro a
    change inner ℂ ξ ((star (a : H →L[ℂ] H)) ξ) =
      star (inner ℂ ξ ((a : H →L[ℂ] H) ξ))
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    exact (inner_conj_symm _ _).symm
  positive := by
    intro a
    change 0 ≤ (inner ℂ ξ ((star (a : H →L[ℂ] H)) ((a : H →L[ℂ] H) ξ))).re
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    exact inner_self_nonneg (𝕜 := ℂ) (x := (a : H →L[ℂ] H) ξ)
  tracial := by
    intro a b
    exact h.2.1 (a : H →L[ℂ] H) (b : H →L[ℂ] H) a.property b.property

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ConcretePredualRepresentation
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.ConcretePredual.evaluationLinearIsometry_apply _root_.OAI.Invariant233.ConcretePredual.norm_evaluation _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233.ConcretePredual

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem representingOperator_mem (M : VonNeumannAlgebra H)
    (Φ : StrongDual ℂ (StrongDual ℂ M)) : representingOperator M Φ ∈ M := by
  have hmem : representingOperator M Φ ∈ M.commutant.commutant := by
    rw [VonNeumannAlgebra.mem_commutant_iff]
    intro B hB
    ext y
    apply ext_inner_left ℂ
    intro x
    change inner ℂ x (B (representingOperator M Φ y)) =
      inner ℂ x (representingOperator M Φ (B y))
    rw [← ContinuousLinearMap.adjoint_inner_left B (representingOperator M Φ y) x,
      inner_representingOperator, inner_representingOperator]
    congr 1
    ext A
    rw [vectorFunctional_apply, vectorFunctional_apply,
      ContinuousLinearMap.adjoint_inner_left]
    congr 1
    exact congrArg (fun Q : H →L[ℂ] H => Q y)
      ((VonNeumannAlgebra.mem_commutant_iff.mp hB) A A.property).symm
  simpa only [M.commutant_commutant] using hmem

theorem evaluation_surjective (M : VonNeumannAlgebra H) :
    Function.Surjective (evaluation M) := by
  intro ℓ
  obtain ⟨Φ, hΦ, _hΦnorm⟩ := exists_extension_norm_eq (predual M) ℓ
  let A : M := ⟨representingOperator M Φ, representingOperator_mem M Φ⟩
  let Ψ : StrongDual ℂ (StrongDual ℂ M) :=
    Φ - NormedSpace.inclusionInDoubleDual ℂ M A
  have hker : predual M ≤ Ψ.ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro f ⟨⟨x, y⟩, rfl⟩
      change Φ (vectorFunctional M x y) - (vectorFunctional M x y) A = 0
      rw [vectorFunctional_apply]
      change Φ (vectorFunctional M x y) - inner ℂ x (representingOperator M Φ y) = 0
      simp
    · exact Ψ.isClosed_ker
  refine ⟨A, ?_⟩
  ext f
  have hf := hker f.property
  change Φ (f : StrongDual ℂ M) - (f : StrongDual ℂ M) A = 0 at hf
  rw [evaluation_apply, ← sub_eq_zero.mp hf]
  exact hΦ f

end Invariant233.ConcretePredual

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ConcretePredualComplete
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233.ConcretePredual

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.Invariant233.ConcretePredual.completedPredualNormedAddCommGroup
local instance completedPredualNormedSpace (M : VonNeumannAlgebra H) :
    NormedSpace ℂ (predual M) := (predual M).normedSpace

def evaluationLinearIsometryEquiv (M : VonNeumannAlgebra H) :
    M ≃ₗᵢ[ℂ] StrongDual ℂ (predual M) :=
  LinearIsometryEquiv.ofSurjective (evaluationLinearIsometry M)
    (evaluation_surjective M)

@[simp]
theorem evaluationLinearIsometryEquiv_apply (M : VonNeumannAlgebra H) (A : M) :
    evaluationLinearIsometryEquiv M A = evaluation M A := rfl

end Invariant233.ConcretePredual

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ContinuityCoboundary
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace InvariantProjection.Continuity

variable {X : Type*}

@[simp] theorem backwardSum_zero (σ : X ≃ X) (v : X → ℝ) (x : X) :
    backwardSum σ v 0 x = 0 := by
  simp [backwardSum]

end InvariantProjection.Continuity

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_Fejer
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Invariant233.Fejer

def geometricPolynomial (H : ℕ) (x : Circle) : ℂ :=
  ∑ k ∈ Finset.range H, fourier (k : ℤ) x

def kernel (H : ℕ) (x : Circle) : ℝ :=
  Complex.normSq (geometricPolynomial H x) / H

def coefficient (H : ℕ) (n : ℤ) : ℂ :=
  fourierCoeff (fun x : Circle => (kernel H x : ℂ)) n

end Invariant233.Fejer

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FejerKernel
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ComplexConjugate

namespace Invariant233.Fejer

 theorem continuous_geometricPolynomial (H : ℕ) : Continuous (geometricPolynomial H) := by
  unfold geometricPolynomial
  exact continuous_finsetSum _ (fun _ _ => (fourier _).continuous)

 theorem continuous_kernel (H : ℕ) : Continuous (kernel H) := by
  unfold kernel
  simpa only [Complex.normSq_eq_norm_sq, Pi.pow_apply] using
    ((continuous_geometricPolynomial H).norm.pow 2).div_const (H : ℝ)

end Invariant233.Fejer

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_FejerApproximation
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.Fejer

def approximation (H : ℕ) (f : Circle → ℝ) (x : Circle) : ℝ :=
  ∫ y, kernel H (x - y) * f y

def approximationCoefficient (H : ℕ) (f : Circle → ℝ) (v : ℤ) : ℂ :=
  coefficient H v * ∫ y, fourier (-v) y * (f y : ℂ)

end Invariant233.Fejer

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FejerApproximation
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Invariant233.Fejer

def bundledKernel (H : ℕ) : C(UnitAddCircle, ℝ) :=
  ⟨kernel H, continuous_kernel H⟩

end Invariant233.Fejer

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_WeightedShiftAlgebra
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal ComplexConjugate
namespace Invariant233.WeightedShift

theorem shift_add (m n : ℤ) :
    (shift (m + n)).toLinearIsometry.toContinuousLinearMap =
      (shift m).toLinearIsometry.toContinuousLinearMap *
        (shift n).toLinearIsometry.toContinuousLinearMap := by
  ext ξ k
  change ξ (k - (m + n)) = ξ (k - m - n)
  exact congrArg (fun q : ℤ => ξ q) (by omega)

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FieldDiagonal
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
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

theorem fieldDiagonal_coordinate_ae (f : Lp Hilbert 2 μ) :
    ∀ᵐ x ∂μ, ∀ k : ℤ, fieldDiagonal a C hC ha hm f x k = a x k * f x k := by
  filter_upwards [fieldDiagonal_ae a C hC ha hm f] with x hx k
  exact congrArg (fun v : Hilbert => v k) hx

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FieldMultiplierAdjoint
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
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

def boundedFieldWeight (a : X → ℤ → ℂ) (ha : ∀ x k, ‖a x k‖ ≤ 1)
    (x : X) : Weight :=
  ⟨a x, memℓp_infty ⟨1, by rintro r ⟨k, rfl⟩; exact ha x k⟩⟩

omit [MeasurableSpace X] in
theorem boundedFieldWeight_norm (a : X → ℤ → ℂ) (ha : ∀ x k, ‖a x k‖ ≤ 1)
    (x : X) : ‖boundedFieldWeight a ha x‖ ≤ 1 :=
  lp.norm_le_of_forall_le (by norm_num) (ha x)

def boundedField (a : X → ℤ → ℂ) (ha : ∀ x k, ‖a x k‖ ≤ 1)
    (hm : ∀ k, AEStronglyMeasurable (fun x => a x k) μ) :
    FieldHilbert μ →L[ℂ] FieldHilbert μ :=
  fieldDiagonal (boundedFieldWeight a ha) 1 (by norm_num)
    (boundedFieldWeight_norm a ha) hm

theorem boundedField_ae (a : X → ℤ → ℂ) (ha : ∀ x k, ‖a x k‖ ≤ 1)
    (hm : ∀ k, AEStronglyMeasurable (fun x => a x k) μ) (ξ : FieldHilbert μ) :
    ∀ᵐ x ∂μ, ∀ k, boundedField a ha hm ξ x k = a x k * ξ x k :=
  fieldDiagonal_coordinate_ae _ _ _ _ _ ξ

def normalizerOperator (h : X → ℤ → ℂ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) :
    FieldHilbert μ →L[ℂ] FieldHilbert μ :=
  boundedField (fun x k => normalizer (h x k))
    (fun x k => normalizer_bound (h x k)) (normalizer_measurable h hm)

def normalizedOperator (h : X → ℤ → ℂ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) :
    FieldHilbert μ →L[ℂ] FieldHilbert μ :=
  boundedField (fun x k => h x k * normalizer (h x k))
    (fun x k => normalized_bound (h x k))
    (fun k => (hm k).mul (normalizer_measurable h hm k))

theorem normalizerOperator_ae (h : X → ℤ → ℂ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) (ξ : FieldHilbert μ) :
    ∀ᵐ x ∂μ, ∀ k, normalizerOperator h hm ξ x k = normalizer (h x k) * ξ x k :=
  boundedField_ae _ _ _ ξ

theorem normalizedOperator_ae (h : X → ℤ → ℂ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) (ξ : FieldHilbert μ) :
    ∀ᵐ x ∂μ, ∀ k, normalizedOperator h hm ξ x k =
      (h x k * normalizer (h x k)) * ξ x k :=
  boundedField_ae _ _ _ ξ

theorem normalizer_mem_domain (h : X → ℤ → ℂ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) (ξ : FieldHilbert μ) :
    normalizerOperator h hm ξ ∈ (fieldUnboundedMultiplier μ h).domain := by
  apply (mem_fieldUnboundedMultiplier_domain_iff h _).mpr
  refine ⟨normalizedOperator h hm ξ, ?_⟩
  filter_upwards [normalizerOperator_ae h hm ξ, normalizedOperator_ae h hm ξ]
    with x hR hS
  intro k
  rw [hR, hS, mul_assoc]

def normalizedStarOperator (h : X → ℤ → ℂ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) :
    FieldHilbert μ →L[ℂ] FieldHilbert μ :=
  boundedField (fun x k => star (h x k * normalizer (h x k)))
    (fun x k => by simpa only [norm_star] using normalized_bound (h x k))
    (fun k => ((hm k).mul (normalizer_measurable h hm k)).star)

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FieldMultiplierCutoff
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
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

theorem boundedOperator_ae (a : X → ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ x k, ‖a x k‖ ≤ C)
    (hm : ∀ k, AEStronglyMeasurable (fun x => a x k) μ) (ξ : FieldHilbert μ) :
    ∀ᵐ x ∂μ, ∀ k, boundedOperator a C hC ha hm ξ x k = a x k * ξ x k :=
  fieldDiagonal_coordinate_ae _ _ _ _ _ ξ

theorem projection_ae (h : X → ℤ → ℝ) (hm : ∀ k, Measurable (fun x => h x k))
    (n : ℕ) (ξ : FieldHilbert μ) :
    ∀ᵐ x ∂μ, ∀ k, projection h hm n ξ x k = symbol n (h x k) * ξ x k :=
  boundedOperator_ae _ _ _ _ _ ξ

theorem productOperator_ae (h : X → ℤ → ℝ) (hm : ∀ k, Measurable (fun x => h x k))
    (n : ℕ) (ξ : FieldHilbert μ) :
    ∀ᵐ x ∂μ, ∀ k, productOperator h hm n ξ x k = productSymbol n (h x k) * ξ x k :=
  boundedOperator_ae _ _ _ _ _ ξ

theorem inverseOperator_ae (h : X → ℤ → ℝ) (hm : ∀ k, Measurable (fun x => h x k))
    (n : ℕ) (ξ : FieldHilbert μ) :
    ∀ᵐ x ∂μ, ∀ k, inverseOperator h hm n ξ x k = inverseSymbol n (h x k) * ξ x k :=
  boundedOperator_ae _ _ _ _ _ ξ

theorem projection_mem_domain (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) (ξ : FieldHilbert μ) :
    projection h hm n ξ ∈ (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).domain := by
  apply (mem_fieldUnboundedMultiplier_domain_iff _ _).mpr
  refine ⟨productOperator h hm n ξ, ?_⟩
  filter_upwards [projection_ae h hm n ξ, productOperator_ae h hm n ξ] with x hP hT
  intro k
  rw [hP, hT]
  exact mul_assoc _ _ _

theorem projection_range_le_domain (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) :
    (projection h hm n).range ≤
      (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).domain := by
  rintro ξ ⟨η, rfl⟩
  exact projection_mem_domain h hm n η

theorem inverseOperator_mem_domain (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) (ξ : FieldHilbert μ) :
    inverseOperator h hm n ξ ∈
      (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).domain := by
  apply (mem_fieldUnboundedMultiplier_domain_iff _ _).mpr
  refine ⟨projection h hm n ξ, ?_⟩
  filter_upwards [projection_ae h hm n ξ, inverseOperator_ae h hm n ξ] with x hP hI
  intro k
  rw [hP, hI, ← mul_assoc, real_mul_inverseSymbol]

theorem multiplier_inverseOperator (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) (ξ : FieldHilbert μ) :
    fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))
      ⟨inverseOperator h hm n ξ, inverseOperator_mem_domain h hm n ξ⟩ = projection h hm n ξ := by
  apply fieldUnboundedMultiplier_eq_of_ae
  filter_upwards [projection_ae h hm n ξ, inverseOperator_ae h hm n ξ] with x hP hI
  intro k
  rw [hP, hI, ← mul_assoc, real_mul_inverseSymbol]

theorem projection_mem_inverse_domain (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) (ξ : FieldHilbert μ) :
    projection h hm n ξ ∈
      (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).inverse.domain := by
  rw [LinearPMap.inverse_domain]
  exact ⟨⟨inverseOperator h hm n ξ, inverseOperator_mem_domain h hm n ξ⟩,
    multiplier_inverseOperator h hm n ξ⟩

theorem projection_range_le_inverse_domain (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) :
    (projection h hm n).range ≤
      (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).inverse.domain := by
  rintro ξ ⟨η, rfl⟩
  exact projection_mem_inverse_domain h hm n η

end Invariant233.WeightedShift.SpectralCutoff

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_FiniteKernelMixture
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Invariant233.FiniteKernelMixture

variable {I X Y : Type*} [Fintype I] [MeasurableSpace X] [MeasurableSpace Y]

noncomputable def diagonalReplacementKernel (q : ℝ≥0∞) (p : I → ℝ≥0∞)
    (u : I → X → ℝ≥0∞) (hu : ∀ i, Measurable (u i))
    (ν : I → Measure X) : Kernel X X :=
  normalizedKernel
    (fun o : Option I => match o with
      | none => Kernel.id
      | some i => Kernel.const X (ν i))
    (fun o x => match o with
      | none => q
      | some i => p i * u i x)
    (fun o => by cases o with
      | none => exact measurable_const
      | some i => exact measurable_const.mul (hu i))

end Invariant233.FiniteKernelMixture

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FiniteKernelMixture
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace Invariant233.FiniteKernelMixture

variable {I X Y : Type*} [Fintype I] [MeasurableSpace X] [MeasurableSpace Y]

@[simp] theorem weightedKernel_apply (κ : I → Kernel X Y) (w : I → X → ℝ≥0∞)
    (hw : ∀ i, Measurable (w i)) (x : X) :
    weightedKernel κ w hw x = ∑ i, w i x • κ i x := rfl

@[simp] theorem normalizedKernel_apply (κ : I → Kernel X Y) (w : I → X → ℝ≥0∞)
    (hw : ∀ i, Measurable (w i)) (x : X) :
    normalizedKernel κ w hw x = ∑ i, (w i x / ∑ j, w j x) • κ i x := rfl

end Invariant233.FiniteKernelMixture

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_LaurentWindow
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Invariant233.LaurentWindow

open Polynomial LaurentPolynomial

variable {R : Type*} [Semiring R]

theorem coeff_fin_sum_monomial_above (N n : ℕ) (a : Fin N → R) (hn : N ≤ n) :
    (∑ j : Fin N, Polynomial.monomial (j : ℕ) (a j)).coeff n = 0 := by
  classical
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  apply Finset.sum_eq_zero
  intro j _
  rw [ite_eq_right]
  omega

theorem trunc_shift_eq_fin_sum (K : ℕ) (A : LaurentPolynomial R)
    (hA : ∀ i : ℤ, (K : ℤ) < i → A.coeff i = 0) :
    LaurentPolynomial.trunc (A * LaurentPolynomial.T (K : ℤ)) =
      ∑ i : Fin (2 * K + 1), Polynomial.monomial (i : ℕ)
        (A.coeff ((i : ℤ) - (K : ℤ))) := by
  ext n
  by_cases hn : n < 2 * K + 1
  · exact (coeff_trunc_mul_T A (K : ℤ) n).trans
      (coeff_fin_sum_monomial (2 * K + 1)
        (fun i : Fin (2 * K + 1) => A.coeff ((i : ℤ) - (K : ℤ))) ⟨n, hn⟩).symm
  · rw [coeff_fin_sum_monomial_above _ n _ (le_of_not_gt hn),
      coeff_trunc_shift_above K n A hA (by omega)]


end Invariant233.LaurentWindow

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_LaurentNoncancellation
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Invariant233.LaurentWindow

open InvariantProjection.FiniteConvolution

theorem laurent_lower_bound_of_finite_bound (K : ℕ) (D δ ε : ℝ)
    (hbound : ∀ a b : Coefficients K,
      (∀ i, ‖a i‖ ≤ D) → (∀ i, ‖b i‖ ≤ D) →
      δ ≤ ‖a (center K)‖ → δ ≤ ‖b (center K)‖ →
      ∃ n : Fin (2 * K + 1), ε ≤ ‖lowProduct a b n‖) :
    ∀ A B : LaurentPolynomial ℂ,
      (∀ i : ℤ, i < -(K : ℤ) ∨ (K : ℤ) < i → A.coeff i = 0) →
      (∀ i : ℤ, i < -(K : ℤ) ∨ (K : ℤ) < i → B.coeff i = 0) →
      (∀ i : ℤ, ‖A.coeff i‖ ≤ D) →
      (∀ i : ℤ, ‖B.coeff i‖ ≤ D) →
      δ ≤ ‖A.coeff 0‖ → δ ≤ ‖B.coeff 0‖ →
      ∃ n : ℕ, n ≤ 2 * K ∧ ε ≤ ‖(A * B).coeff (-(n : ℤ))‖ := by
  intro A B hAs hBs hA hB hA0 hB0
  let a : Coefficients K := fun i => A.coeff ((i : ℤ) - (K : ℤ))
  let b : Coefficients K := fun i => B.coeff ((i : ℤ) - (K : ℤ))
  have ha0 : δ ≤ ‖a (center K)‖ := by simpa [a, center] using hA0
  have hb0 : δ ≤ ‖b (center K)‖ := by simpa [b, center] using hB0
  obtain ⟨n, hn⟩ := hbound a b (fun i => hA _) (fun i => hB _) ha0 hb0
  have hpa : polynomial a = LaurentPolynomial.trunc
      (A * LaurentPolynomial.T (K : ℤ)) :=
    (trunc_shift_eq_fin_sum K A (fun i hi => hAs i (Or.inr hi))).symm
  have hpb : polynomial b = LaurentPolynomial.trunc
      (B * LaurentPolynomial.T (K : ℤ)) :=
    (trunc_shift_eq_fin_sum K B (fun i hi => hBs i (Or.inr hi))).symm
  have hc : lowProduct a b n = (A * B).coeff ((n : ℤ) - 2 * (K : ℤ)) := by
    unfold lowProduct
    rw [hpa, hpb]
    exact coeff_shifted_product K (n : ℕ) A B
      (fun i hi => hAs i (Or.inl hi)) (fun i hi => hBs i (Or.inl hi))
  refine ⟨2 * K - (n : ℕ), Nat.sub_le _ _, ?_⟩
  have he : -((2 * K - (n : ℕ) : ℕ) : ℤ) = (n : ℤ) - 2 * (K : ℤ) := by
    have := n.isLt
    omega
  rw [he, ← hc]
  exact hn

end Invariant233.LaurentWindow

namespace Invariant233.FiniteWindow

open Invariant233.LaurentWindow
open InvariantProjection.FiniteConvolution

theorem convolution_lower_bound_of_finite_bound (K : ℕ) (D δ ε : ℝ)
    (hfinite : ∀ a b : Coefficients K,
      (∀ i, ‖a i‖ ≤ D) → (∀ i, ‖b i‖ ≤ D) →
      δ ≤ ‖a (center K)‖ → δ ≤ ‖b (center K)‖ →
      ∃ n : Fin (2 * K + 1), ε ≤ ‖lowProduct a b n‖) :
    ∀ a b : ℤ → ℂ,
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖a i‖ ≤ D) →
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖b i‖ ≤ D) →
      δ ≤ ‖a 0‖ → δ ≤ ‖b 0‖ →
      ∃ n : ℕ, n ≤ 2 * K ∧ ε ≤ ‖convolution K a b n‖ := by
  have hbound := laurent_lower_bound_of_finite_bound K D δ ε hfinite
  intro a b ha hb ha0 hb0
  have hD : 0 ≤ D := (norm_nonneg (a 0)).trans (ha 0 (by simp))
  have support_zero : ∀ c : ℤ → ℂ, ∀ i : ℤ,
      i < -(K : ℤ) ∨ (K : ℤ) < i → (laurent K c).coeff i = 0 := by
    intro c i hi
    rw [laurent_coeff, ite_eq_right]
    simp only [abs_le]
    omega
  have coeff_bound : ∀ c : ℤ → ℂ,
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖c i‖ ≤ D) →
      ∀ i : ℤ, ‖(laurent K c).coeff i‖ ≤ D := by
    intro c hc i
    rw [laurent_coeff]
    split_ifs with hi
    · exact hc i hi
    · simpa only [norm_zero] using hD
  obtain ⟨n, hn, hnc⟩ := hbound (laurent K a) (laurent K b)
    (support_zero a) (support_zero b) (coeff_bound a ha) (coeff_bound b hb)
    (by simpa only [laurent_coeff_zero] using ha0)
    (by simpa only [laurent_coeff_zero] using hb0)
  exact ⟨n, hn, by simpa only [coeff_laurent_product] using hnc⟩

theorem uniform_convolution_lower_bound (K : ℕ) (D δ : ℝ) (hδ : 0 < δ) :
    ∃ ε > 0, ∀ a b : ℤ → ℂ,
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖a i‖ ≤ D) →
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖b i‖ ≤ D) →
      δ ≤ ‖a 0‖ → δ ≤ ‖b 0‖ →
      ∃ n : ℕ, n ≤ 2 * K ∧ ε ≤ ‖convolution K a b n‖ := by
  obtain ⟨ε, hε, hbound⟩ := uniform_lower_bound K D δ hδ
  exact ⟨ε, hε, convolution_lower_bound_of_finite_bound K D δ ε hbound⟩

end Invariant233.FiniteWindow

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FieldDiagonalConvergence
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
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

theorem diagonal_tendsto_apply {ι : Type*} {l : Filter ι}
    {a : ι → Weight} {b : Weight} {C : ℝ}
    (ha : ∀ᶠ n in l, ‖a n‖ ≤ C)
    (hab : ∀ k : ℤ, Tendsto (fun n => a n k) l (𝓝 (b k))) (v : Hilbert) :
    Tendsto (fun n => diagonal (a n) v) l (𝓝 (diagonal b v)) := by
  let basis : HilbertBasis ℤ ℂ Hilbert := ⟨LinearIsometryEquiv.refl ℂ Hilbert⟩
  have hbasis (k : ℤ) : basis k = (lp.single 2 k (1 : ℂ) : Hilbert) :=
    basis.repr_self k
  apply strong_tendsto_of_dense_span_of_bounded (C := C)
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr basis.dense_span) ?_ ?_ v
  · intro k
    have hs : ∀ w : Weight, diagonal w (basis k) = w k • basis k := by
      intro w
      rw [hbasis]
      apply lp.ext
      funext j
      change w j * (lp.single 2 k (1 : ℂ) : Hilbert) j = w k * (lp.single 2 k (1 : ℂ) : Hilbert) j
      by_cases hj : j = k
      · subst j; rfl
      · simp [lp.single_apply, hj]
    simp_rw [hs]
    exact (hab k).smul_const (basis k)
  · filter_upwards [ha] with n hn
    exact (lp.norm_mapCLM_le 2 _ (norm_nonneg (a n)) _).trans hn

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_Rotation
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Invariant233.Rotation

theorem action_continuous (θ : ℝ) (k : ℤ) : Continuous (action θ k) :=
  continuous_id.add continuous_const

theorem action_measurePreserving (θ : ℝ) (k : ℤ) :
    MeasurePreserving (action θ k) circleMeasure circleMeasure := by
  change MeasurePreserving (fun x : Circle => x + k • (θ : Circle)) volume volume
  exact measurePreserving_add_right volume (k • (θ : Circle))

theorem U_ae (ξ : Hilbert) :
    U ξ =ᵐ[circleMeasure] fun x => WeightedShift.shift 1 (ξ x) :=
  ContinuousLinearMap.coeFn_compLpL _ _

theorem U_coordinates_ae (ξ : Hilbert) :
    ∀ᵐ x ∂circleMeasure, ∀ k : ℤ, U ξ x k = ξ x (k - 1) := by
  filter_upwards [U_ae ξ] with x hx
  intro k
  rw [hx]
  rfl

theorem weighted_coordinates_ae (θ : ℝ) (a : C(Circle, ℂ)) (ξ : Hilbert) :
    ∀ᵐ x ∂circleMeasure, ∀ k : ℤ,
      weighted θ a ξ x k = a (action θ (k - 1) x) * ξ x (k - 1) := by
  filter_upwards [U_coordinates_ae (representation θ a ξ),
      representation_coordinates_ae θ a ξ] with x hU ha
  intro k
  exact (hU k).trans (ha (k - 1))

def representationStarAlgHom (θ : ℝ) : C(Circle, ℂ) →⋆ₐ[ℂ] (Hilbert →L[ℂ] Hilbert) where
  toFun := representation θ
  map_one' := representation_one θ
  map_mul' := representation_mul θ
  map_zero' := representation_zero θ
  map_add' := representation_add θ
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, representation_smul, representation_one]
  map_star' := representation_star θ

end Invariant233.Rotation

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_RotationMeasurable
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Invariant233

namespace Rotation

theorem measurableRepresentation_coordinates_ae
    (θ : ℝ) (g : Circle → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) (v : Hilbert) :
    ∀ᵐ x ∂circleMeasure, ∀ k : ℤ,
      measurableRepresentation θ g C hC hg hb v x k = g (action θ k x) * v x k :=
  WeightedShift.fieldDiagonal_coordinate_ae _ _ _ _ _ v

theorem U_mul_measurableRepresentation_coordinates_ae
    (θ : ℝ) (g : Circle → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) (v : Hilbert) :
    ∀ᵐ x ∂circleMeasure, ∀ k : ℤ,
      (U * measurableRepresentation θ g C hC hg hb) v x k =
        g (action θ (k - 1) x) * v x (k - 1) := by
  filter_upwards [U_coordinates_ae (measurableRepresentation θ g C hC hg hb v),
    measurableRepresentation_coordinates_ae θ g C hC hg hb v] with x hU hg
  intro k
  exact (hU k).trans (hg (k - 1))

end Rotation
end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_StrongFourierRecovery
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace Invariant233
namespace StrongFourierRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def average (C : ℤ → H →L[ℂ] H) (N : ℕ) : H →L[ℂ] H :=
  ∑ r ∈ Fejer.frequencies N, Fejer.coefficient N r • C r

end StrongFourierRecovery
end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSampling
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingCylinderWeak.quotient_cutCoordinates _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter MeasureTheory Set
open scoped ENNReal Topology BigOperators

namespace Invariant233.ProductModel.Sampling

@[fun_prop]
theorem selectedEndpoint_measurable (I : Finset ℕ) :
    Measurable (fun xz : EndpointPair => selectedEndpoint I xz.1 xz.2) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i ∈ I
  · simpa [selectedEndpoint, hi, Function.comp_def] using (measurable_pi_apply i).comp measurable_snd
  · simpa [selectedEndpoint, hi, Function.comp_def] using (measurable_pi_apply i).comp measurable_fst

@[fun_prop]
theorem endpointMap_measurable (I : Finset ℕ) :
    Measurable (fun xz : EndpointPair => (xz.1, selectedEndpoint I xz.1 xz.2)) :=
  measurable_fst.prodMk (selectedEndpoint_measurable I)

end Invariant233.ProductModel.Sampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_TriangularSecondMarginal
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal

namespace Invariant233.ProductModel.Sampling

def reverseTriangularEvent (I : Finset ℕ) : Set EndpointPair :=
  {xz | ∀ i ∈ I, circleRepresentative (xz.2 i) < circleRepresentative (xz.1 i)}

end Invariant233.ProductModel.Sampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_OneCoordinateCoupling
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.baseLaw_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Invariant233.OneCoordinateCoupling

open CouplingMarginalBounds CouplingMixture

noncomputable def pairLaw (κ m a b t : ℝ) : Measure (ℝ × ℝ) :=
  mixture baseLaw (ENNReal.ofReal (diagonalMass κ m a b t))
    (fun i => ENNReal.ofReal (componentProbabilities κ m a b t i))
    (leftLaw m a b) (rightLaw m a b)

instance labelMeasurableSingletonClass : MeasurableSingletonClass (Option (Fin 5)) :=
  ⟨fun _ => trivial⟩

noncomputable def leftMarginalDensity (κ m a b t x : ℝ) : ℝ :=
  diagonalMass κ m a b t +
    ∑ i, componentProbabilities κ m a b t i * leftDensity m a b i x

noncomputable def rightMarginalDensity (κ m a b t x : ℝ) : ℝ :=
  diagonalMass κ m a b t +
    ∑ i, componentProbabilities κ m a b t i * rightDensity m a b i x

end Invariant233.OneCoordinateCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_OneCoordinateCoupling
attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Invariant233.OneCoordinateCoupling

open CouplingMarginalBounds CouplingMixture

lemma pairLaw_isProbabilityMeasure {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) : IsProbabilityMeasure (pairLaw κ m a b t) := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have : ∀ i, IsProbabilityMeasure (leftLaw m a b i) :=
    leftLaw_isProbabilityMeasure hm0 ha0 ha' hb0 hb'
  have : ∀ i, IsProbabilityMeasure (rightLaw m a b i) :=
    rightLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb'
  apply mixture_isProbabilityMeasure
  have hq0 : 0 ≤ diagonalMass κ m a b t :=
    le_trans (by norm_num) (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
  have hp0 := componentProbabilities_nonneg (a := a) (b := b) hκ0 hm0 ht0
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp0 i),
    ← ENNReal.ofReal_add hq0 (Finset.sum_nonneg (fun i _ => hp0 i))]
  have htotal : diagonalMass κ m a b t + ∑ i, componentProbabilities κ m a b t i = 1 := by
    simp only [componentProbabilities, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
    unfold diagonalMass
    ring
  rw [htotal]
  norm_num

lemma labelledLaw_map_snd (κ m a b t : ℝ) :
    (labelledLaw κ m a b t).map Prod.snd = pairLaw κ m a b t :=
  labelledMixture_map_snd _ _ _ _ _

lemma labelledLaw_isProbabilityMeasure {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) : IsProbabilityMeasure (labelledLaw κ m a b t) := by
  have := pairLaw_isProbabilityMeasure hκ0 hκ hm ha ha' hb hb' ht0 ht
  constructor
  have h := congrArg (fun ν : Measure (ℝ × ℝ) => ν Set.univ)
    (labelledLaw_map_snd κ m a b t)
  simpa [Measure.map_apply measurable_snd MeasurableSet.univ] using h

end Invariant233.OneCoordinateCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_PrefixHybrid
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingCylinderWeak.quotient_cutCoordinates _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Invariant233.ProductModel

@[simp] theorem prefixEndpoint_apply (D i : ℕ) (x y : Base) :
    prefixEndpoint D x y i = if i < D then y i else x i := by
  simp [prefixEndpoint, selectedEndpoint]

@[simp] theorem prefixPair_fst (D : ℕ) (xy : EndpointPair) :
    (prefixPair D xy).1 = xy.1 := rfl

instance prefixPairLaw_finite (ν : Measure EndpointPair) [IsFiniteMeasure ν] (D : ℕ) :
    IsFiniteMeasure (prefixPairLaw ν D) := by
  unfold prefixPairLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_ProductCocycle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Invariant233.ProductCocycle

def haar (I : Type*) : Measure (Space I) :=
  Measure.infinitePi (fun _ : I ↦ (volume : Measure UnitAddCircle))

def rotate {I : Type*} (θ : I → ℝ) (k : ℤ) (x : Space I) : Space I :=
  fun i ↦ x i + (((k : ℝ) * θ i : ℝ) : UnitAddCircle)

end Invariant233.ProductCocycle

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_ProductPairIdentity
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233.ProductModel

def cocycleRatio (θ c : ℕ → ℝ) (x y : Base) (k : ℤ) : ℝ :=
  ProductCocycle.cocycleVersion θ c k y / ProductCocycle.cocycleVersion θ c k x

def ratioDiagonal (θ c : ℕ → ℝ) (x y : Base) : Fiber →L[ℂ] Fiber :=
  SequenceHilbert.boundedDiagonal (fun k => (cocycleRatio θ c x y k : ℂ))

def PairIdentity (θ c : ℕ → ℝ) (F : Base → Fiber →L[ℂ] Fiber)
    (xy : EndpointPair) : Prop :=
  (∀ k : ℤ, 0 < cocycleRatio θ c xy.1 xy.2 k ∧
    cocycleRatio θ c xy.1 xy.2 k ≤ 1) ∧
  (1 - F xy.2) * ratioDiagonal θ c xy.1 xy.2 * F xy.1 = 0

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductCocycle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Function

namespace Invariant233.ProductCocycle

@[simp] theorem rotate_zero {I : Type*} (θ : I → ℝ) (x : Space I) :
    rotate θ 0 x = x := by
  funext i
  simp [rotate]

theorem rotate_add {I : Type*} (θ : I → ℝ) (k n : ℤ) (x : Space I) :
    rotate θ (k + n) x = rotate θ n (rotate θ k x) := by
  funext i
  simp only [rotate, Int.cast_add, add_mul, AddCircle.coe_add, add_assoc]

@[simp] theorem coe_representative (x : UnitAddCircle) :
    ((representative x : ℝ) : UnitAddCircle) = x :=
  AddCircle.coe_equivIco

theorem measurable_representative : Measurable representative :=
  CocycleSupport.measurePreserving_circleRepresentative.measurable

theorem measurePreserving_rotate {I : Type*} (θ : I → ℝ) (k : ℤ) :
    MeasurePreserving (rotate θ k) (haar I) (haar I) := by
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    ⟨UnitAddCircle.measure_univ⟩
  have hcoord (i : I) : MeasurePreserving
      (fun x : UnitAddCircle ↦ x + (((k : ℝ) * θ i : ℝ) : UnitAddCircle)) volume volume :=
    measurePreserving_add_right volume _
  refine ⟨Measurable.of_eval (fun i ↦ (measurable_pi_apply i).add_const _), ?_⟩
  change (Measure.infinitePi (fun _ : I ↦ (volume : Measure UnitAddCircle))).map
      (fun x i ↦ x i + (((k : ℝ) * θ i : ℝ) : UnitAddCircle)) = _
  rw [Measure.infinitePi_map_pi _ (fun i ↦ (hcoord i).measurable)]
  simp only [(hcoord _).map_eq, haar]

end Invariant233.ProductCocycle

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FieldKoopmanDiagonal
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter

namespace Invariant233.FieldKoopman
open WeightedShift DirectIntegral
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem commute_fieldShifts (m n : ℤ) (σ : X → X)
    (hσ : MeasurePreserving σ μ μ) :
    Commute ((shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ)
      (shiftedPullback (shift n).toLinearIsometry.toContinuousLinearMap σ hσ) := by
  apply commute_const
  change (shift m).toLinearIsometry.toContinuousLinearMap *
      (shift n).toLinearIsometry.toContinuousLinearMap =
    (shift n).toLinearIsometry.toContinuousLinearMap *
      (shift m).toLinearIsometry.toContinuousLinearMap
  rw [← shift_add, ← shift_add, add_comm m n]

theorem commute_fieldDiagonal
    (a : X → Weight) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ x, ‖a x‖ ≤ C)
    (hm : ∀ k, AEStronglyMeasurable (fun x => a x k) μ)
    (m : ℤ) (σ : X → X) (hσ : MeasurePreserving σ μ μ)
    (hcoeff : ∀ᵐ x ∂μ, ∀ k : ℤ, a (σ x) (k - m) = a x k) :
    Commute (fieldDiagonal a C hC ha hm)
      (shiftedPullback (shift m).toLinearIsometry.toContinuousLinearMap σ hσ) := by
  apply commute_of_represented_covariance (fieldDiagonal a C hC ha hm)
    (fun x => diagonal (a x)) (fieldDiagonal_ae a C hC ha hm)
    (shift m).toLinearIsometry.toContinuousLinearMap σ hσ
  filter_upwards [hcoeff] with x hx
  ext ξ k
  change a x k * ξ (k - m) = a (σ x) (k - m) * ξ (k - m)
  rw [hx k]

theorem shift_default_basis (m k : ℤ) :
    shift m ((default : HilbertBasis ℤ ℂ Hilbert) k) =
      (default : HilbertBasis ℤ ℂ Hilbert) (k + m) := by
  have hb (i : ℤ) : (default : HilbertBasis ℤ ℂ Hilbert) i =
      (lp.single 2 i (1 : ℂ) : Hilbert) :=
    (HilbertBasis.repr_symm_single (default : HilbertBasis ℤ ℂ Hilbert) i).symm
  rw [hb, hb]
  ext j
  change (lp.single 2 k (1 : ℂ) : Hilbert) (j - m) =
    (lp.single 2 (k + m) (1 : ℂ) : Hilbert) j
  simp [lp.single_apply, Pi.single_apply, sub_eq_iff_eq_add]

end Invariant233.FieldKoopman

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductFields
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.ProductModel

theorem shiftOperator_ae (ξ : Hilbert) :
    shiftOperator ξ =ᵐ[baseMeasure] fun x => WeightedShift.shift 1 (ξ x) :=
  ContinuousLinearMap.coeFn_compLpL _ _

theorem multiplier_ae (θ : ℕ → ℝ) (g : Base → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) (ξ : Hilbert) :
    multiplier θ g C hC hg hb ξ =ᵐ[baseMeasure]
      fun x => WeightedShift.diagonal (multiplierField θ g C hb x) (ξ x) := by
  unfold multiplier
  exact WeightedShift.fieldDiagonal_ae _ _ _ _ _ _

theorem shiftOperator_commutes_multiplier (g : Lp ℂ ∞ baseMeasure) :
    Commute shiftOperator (L2Multiplication.multiplier (E := Fiber) g) :=
  L2Multiplication.commute_multiplier_of_represented shiftOperator
    (fun _ => (WeightedShift.shift 1).toLinearIsometry.toContinuousLinearMap)
    shiftOperator_ae g

theorem multiplier_commutes_scalar (θ : ℕ → ℝ) (g : Base → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C)
    (a : Lp ℂ ∞ baseMeasure) :
    Commute (multiplier θ g C hC hg hb) (L2Multiplication.multiplier (E := Fiber) a) :=
  L2Multiplication.commute_multiplier_of_represented _
    (fun x => WeightedShift.diagonal (multiplierField θ g C hb x))
    (multiplier_ae θ g C hC hg hb) a

theorem scalarMultiplier_mem_commutant (θ : ℕ → ℝ) (g : Lp ℂ ∞ baseMeasure) :
    L2Multiplication.multiplier (E := Fiber) g ∈ (factor θ).commutant := by
  apply (mem_commutant_vonNeumannGenerated_iff _ _).mpr
  intro A hA
  have hcomm : ∀ a : Lp ℂ ∞ baseMeasure,
      Commute A (L2Multiplication.multiplier (E := Fiber) a) := by
    rcases hA with hA | hA
    · rcases Set.mem_singleton_iff.mp hA with rfl
      exact shiftOperator_commutes_multiplier
    · obtain ⟨f, C, hC, hf, hb, rfl⟩ := hA
      exact multiplier_commutes_scalar θ f C hC hf hb
  exact ⟨(hcomm g).eq, (L2Multiplication.star_commutes_multiplier A hcomm g).eq⟩

theorem factor_commutes_scalarMultiplier (θ : ℕ → ℝ) {T : Hilbert →L[ℂ] Hilbert}
    (hT : T ∈ factor θ) (g : Lp ℂ ∞ baseMeasure) :
    Commute T (L2Multiplication.multiplier (E := Fiber) g) :=
  (VonNeumannAlgebra.mem_commutant_iff.mp (scalarMultiplier_mem_commutant θ g)) T hT

theorem exists_unique_field {θ : ℕ → ℝ} {T : Hilbert →L[ℂ] Hilbert}
    (hT : T ∈ factor θ) :
    ∃ F : Base → Fiber →L[ℂ] Fiber,
      (∀ x, ‖F x‖ ≤ ‖T‖) ∧
      (∀ v : Fiber, StronglyMeasurable fun x => F x v) ∧
      (∀ ξ : Hilbert, T ξ =ᵐ[baseMeasure] fun x => F x (ξ x)) ∧
      (∀ G : Base → Fiber →L[ℂ] Fiber,
        (∀ ξ : Hilbert, T ξ =ᵐ[baseMeasure] fun x => G x (ξ x)) →
          F =ᵐ[baseMeasure] G) :=
  L2Multiplication.exists_unique_field_of_commutes
    (default : HilbertBasis ℤ ℂ Fiber) T (factor_commutes_scalarMultiplier θ hT)

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductCovariance
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter

namespace Invariant233.ProductModel

@[simp] theorem rotationIterate_zero (θ : ℕ → ℝ) (x : Base) :
    rotationIterate θ 0 x = x := ProductCocycle.rotate_zero θ x

theorem rotationIterate_add (θ : ℕ → ℝ) (m n : ℤ) (x : Base) :
    rotationIterate θ (m + n) x = rotationIterate θ n (rotationIterate θ m x) :=
  ProductCocycle.rotate_add θ m n x

theorem rotationIterate_measurePreserving (θ : ℕ → ℝ) (m : ℤ) :
    MeasurePreserving (rotationIterate θ m) baseMeasure baseMeasure :=
  ProductCocycle.measurePreserving_rotate θ m

theorem shiftedPullback_mem_unitary (θ : ℕ → ℝ) (m : ℤ) :
    DirectIntegral.shiftedPullback
      (WeightedShift.shift m).toLinearIsometry.toContinuousLinearMap
      (rotationIterate θ m) (rotationIterate_measurePreserving θ m) ∈
        unitary (Hilbert →L[ℂ] Hilbert) := by
  apply FieldKoopman.operator_mem_unitary (WeightedShift.shift m)
    (rotationIterate θ m) (rotationIterate θ (-m))
  · exact rotationIterate_measurePreserving θ (-m)
  · funext x
    change rotationIterate θ (-m) (rotationIterate θ m x) = x
    rw [← rotationIterate_add]
    simp
  · funext x
    change rotationIterate θ m (rotationIterate θ (-m) x) = x
    rw [← rotationIterate_add]
    simp

theorem multiplier_commutes_shiftedPullback (θ : ℕ → ℝ)
    (g : Base → ℂ) (C : ℝ) (hC : 0 ≤ C) (hg : Measurable g)
    (hb : ∀ x, ‖g x‖ ≤ C) (m : ℤ) :
    Commute (multiplier θ g C hC hg hb)
      (DirectIntegral.shiftedPullback
        (WeightedShift.shift m).toLinearIsometry.toContinuousLinearMap
        (rotationIterate θ m) (rotationIterate_measurePreserving θ m)) := by
  unfold multiplier
  apply FieldKoopman.commute_fieldDiagonal
  apply Filter.Eventually.of_forall
  intro x k
  change g (rotationIterate θ (k - m) (rotationIterate θ m x)) =
    g (rotationIterate θ k x)
  rw [← rotationIterate_add]
  congr 2
  omega

theorem commute_shiftedPullback_of_mem_factor (θ : ℕ → ℝ)
    {T : Hilbert →L[ℂ] Hilbert} (hT : T ∈ factor θ) (m : ℤ) :
    Commute T (DirectIntegral.shiftedPullback
      (WeightedShift.shift m).toLinearIsometry.toContinuousLinearMap
      (rotationIterate θ m) (rotationIterate_measurePreserving θ m)) := by
  apply FieldKoopman.commute_of_mem_generated_of_unitary
    ({shiftOperator} ∪ multiplierGenerators θ) (shiftedPullback_mem_unitary θ m) _ hT
  intro A hA
  rcases hA with hA | hA
  · rcases Set.mem_singleton_iff.mp hA with rfl
    exact FieldKoopman.commute_fieldShifts 1 m _ _
  · obtain ⟨g, C, hC, hg, hb, rfl⟩ := hA
    exact multiplier_commutes_shiftedPullback θ g C hC hg hb m

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductTracialVector
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter

namespace Invariant233.ProductModel

theorem traceVector_faithfulTracial (θ : ℕ → ℝ) :
    IsFaithfulTracialVector (factor θ) traceVector := by
  have hb : (default : HilbertBasis ℤ ℂ Fiber) 0 =
      (lp.single 2 (0 : ℤ) (1 : ℂ) : Fiber) :=
    (HilbertBasis.repr_symm_single (default : HilbertBasis ℤ ℂ Fiber) 0).symm
  rw [traceVector, ← hb]
  apply FieldTraceCyclic.faithfulTracialVector_of_commuting_shiftedPullbacks
    (default : HilbertBasis ℤ ℂ Fiber) (factor θ)
    (rotationIterate θ) (rotationIterate_measurePreserving θ)
    (fun m => (WeightedShift.shift m).toLinearIsometry)
  · exact FieldKoopman.shift_default_basis
  · intro T hT
    exact commute_shiftedPullback_of_mem_factor θ hT
  · intro T hT
    obtain ⟨F, hbound, hmeas, hrepr, _⟩ := exists_unique_field hT
    exact ⟨F, hrepr, fun r => (hmeas _).aestronglyMeasurable,
      Filter.Eventually.of_forall hbound⟩

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_CompactTransfer
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped NNReal
noncomputable section

namespace Invariant233

instance sequenceHilbertIntMeasurableSpace : MeasurableSpace (SequenceHilbert ℤ) := borel _

instance sequenceHilbertIntBorelSpace : BorelSpace (SequenceHilbert ℤ) := ⟨rfl⟩

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductWeightBridge
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Function
open scoped ENNReal

namespace Invariant233.ProductModel

theorem measurable_logarithmicCost (θ c : ℕ → ℝ) :
    Measurable (logarithmicCost θ c) := by
  apply Measurable.tsum
  intro i
  have hrep : Measurable (fun x : Base ↦ circleRepresentative (x i)) :=
    ProductCocycle.measurable_representative.comp (measurable_pi_apply i)
  exact (measurable_const.mul ((measurable_of_countable (fun z : ℤ ↦ (z : ℝ))).comp
    ((hrep.add_const (θ i)).floor))).ennreal_ofReal

theorem measurable_weight (θ c : ℕ → ℝ) : Measurable (weight θ c) := by
  exact (((measurable_coe_ennreal_ereal.comp
    (measurable_logarithmicCost θ c)).neg).ereal_exp).ennreal_toReal

end Invariant233.ProductModel

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_WeightedOrbitInvariance
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.WeightedShift.diagonalAlgHom_apply _root_.OAI.Invariant233.WeightedShift.diagonal_add _root_.OAI.Invariant233.WeightedShift.diagonal_mul _root_.OAI.Invariant233.WeightedShift.diagonal_one _root_.OAI.Invariant233.WeightedShift.diagonal_smul _root_.OAI.Invariant233.WeightedShift.diagonal_star _root_.OAI.Invariant233.WeightedShift.diagonal_zero _root_.OAI.Invariant233.WeightedShift.shift_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233.OrbitInvariance
open WeightedShift

abbrev shiftMap (n : ℤ) : Hilbert →L[ℂ] Hilbert :=
  (shift n).toLinearIsometry.toContinuousLinearMap

theorem shiftMap_mul_neg (n : ℤ) :
    shiftMap n * shiftMap (-n) = 1 := by
  ext ξ k
  simp [shiftMap, shift_apply]

def shiftUnit (n : ℤ) : (Hilbert →L[ℂ] Hilbert)ˣ where
  val := shiftMap n
  inv := shiftMap (-n)
  val_inv := shiftMap_mul_neg n
  inv_val := by simpa using shiftMap_mul_neg (-n)

end Invariant233.OrbitInvariance

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductOrbitPair
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators

namespace Invariant233.ProductModel

def actualWeightField (θ c : ℕ → ℝ) (x : Base) : WeightedShift.Weight :=
  multiplierField θ (fun y => (weight θ c y : ℂ)) 1 (fun y => by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (weight_mem_Icc θ c y).1] using (weight_mem_Icc θ c y).2) x

@[simp] theorem actualWeightField_apply (θ c : ℕ → ℝ) (x : Base) (k : ℤ) :
    actualWeightField θ c x k = (weight θ c (rotationIterate θ k x) : ℂ) := rfl

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductPairTransfer
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Invariant233.ProductModel

local instance instOpensMeasurableSpaceEndpointPair : OpensMeasurableSpace EndpointPair := inferInstance

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_ProductScales
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Invariant233

namespace ProductScaleData

def prefixCount (p : ProductScaleData) (n : ℕ) : ℕ :=
  ∑ r ∈ Finset.range n, p.m r

def prefixCost (p : ProductScaleData) (n : ℕ) : ℝ :=
  ∑ r ∈ Finset.range n, p.C r * p.m r

def coefficientBound (p : ProductScaleData) (n : ℕ) : ℝ :=
  Real.exp (((p.K n : ℝ) + 1) * p.prefixCost n)

def N (p : ProductScaleData) (n : ℕ) : ℝ := (p.m n : ℝ) * p.K n

end ProductScaleData

open Invariant233.FiniteWindow

structure ProductScaleLaws (p : ProductScaleData) : Prop where
  initial_K : p.K 0 = 100
  initial_G : p.G 0 = 1
  K_pos : ∀ n, 0 < p.K n
  G_pos : ∀ n, 0 < p.G n
  epsilon_pos : ∀ n, 0 < p.ε n
  L_ge_one : ∀ n, 1 ≤ p.L n
  L_monotone : Monotone p.L
  C_eq : ∀ n, p.C n = max (p.L n) ((p.K n : ℝ) ^ 2)
  polynomial_lower : ∀ n, ∀ A B : ℤ → ℂ,
    (∀ i, |i| ≤ (p.K n : ℤ) → ‖A i‖ ≤ p.coefficientBound n) →
    (∀ i, |i| ≤ (p.K n : ℤ) → ‖B i‖ ≤ p.coefficientBound n) →
    1 / ((n + 1 : ℕ) : ℝ) ≤ ‖A 0‖ →
    1 / ((n + 1 : ℕ) : ℝ) ≤ ‖B 0‖ →
    ∃ i : ℕ, i ≤ 2 * p.K n ∧ p.ε n ≤ ‖convolution (p.K n) A B i‖
  polynomial_attenuation : ∀ n,
    ((2 * p.K n + 1 : ℕ) : ℝ) * 3 * Real.exp (-p.L n / 10000) ≤
      p.ε n / ((n + 1 : ℕ) : ℝ)
  gain_attenuation : ∀ n,
    p.L n ≤ ProductScaleData.kappa (n + 1) * Real.sqrt (p.G (n + 1) : ℝ)
  m_ge_K : ∀ n, p.K n ≤ p.m n
  m_ge_pow : ∀ n, 2 ^ (n + 1) ≤ p.m n
  m_ge_G : ∀ n, 4 * p.G n ≤ p.m n
  m_ge_100 : ∀ n, 100 ≤ p.m n
  prefix_count_le : ∀ n, (p.prefixCount n : ℝ) ≤ (p.m n : ℝ) / 100
  m_attenuation : ∀ n,
    p.L n ≤ ProductScaleData.kappa n * (p.m n : ℝ) ^ (1 / 40 : ℝ)
  next_K : ∀ n,
    p.K (n + 1) = ⌈(p.m n : ℝ) ^ ((3 / 4 : ℝ) * p.m n)⌉₊
  next_gap : ∀ n, (p.G (n + 1) : ℝ) * p.K (n + 1) <
    (p.m n : ℝ) ^ ((4 / 5 : ℝ) * p.m n)
  K_double : ∀ n, 2 * p.K n < p.K (n + 1)

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductScaleConsequences
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter
namespace Invariant233.ProductScaleLaws

variable {p : ProductScaleData} (hp : ProductScaleLaws p)
include hp

theorem m_pos (n : ℕ) : 0 < p.m n := by have := hp.m_ge_100 n; omega

theorem a_bounds (n : ℕ) :
    1 / (p.m n : ℝ) ≤ p.a n ∧ p.a n ≤ 1 / 4 := by
  have hm : 0 < (p.m n : ℝ) := by exact_mod_cast hp.m_pos n
  have hG : (1 : ℝ) ≤ p.G n := by exact_mod_cast hp.G_pos n
  have hlarge : 4 * (p.G n : ℝ) ≤ p.m n := by exact_mod_cast hp.m_ge_G n
  dsimp [ProductScaleData.a]
  constructor
  · exact div_le_div_of_nonneg_right hG hm.le
  · apply (div_le_iff₀ hm).mpr
    linarith

theorem b_bounds (n : ℕ) :
    1 / (p.m n : ℝ) ≤ p.b n ∧ p.b n ≤ 1 / 4 := by
  have hm100 : (100 : ℝ) ≤ p.m n := by exact_mod_cast hp.m_ge_100 n
  have hm1 : (1 : ℝ) ≤ p.m n := by linarith
  have hm : (0 : ℝ) < p.m n := by linarith
  dsimp [ProductScaleData.b]
  constructor
  · rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
  · calc
      (p.m n : ℝ) ^ (-(19 / 20 : ℝ)) ≤ (p.m n : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
      _ = (Real.sqrt (p.m n : ℝ))⁻¹ := by rw [Real.rpow_neg hm.le, ← Real.sqrt_eq_rpow]
      _ ≤ 1 / 4 := by
        have hs : (4 : ℝ) ≤ Real.sqrt (p.m n : ℝ) := by
          apply Real.le_sqrt_of_sq_le
          linarith
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hs

end Invariant233.ProductScaleLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_ProductCoupling
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.baseLaw_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Invariant233.OrderedProductCoupling

open OneCoordinateCoupling

noncomputable def coordinateLaw (P : Parameters) (i : ℕ) : Measure CoordinateSample :=
  labelledLaw (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i)

noncomputable def law (P : Parameters) : Measure Sample :=
  Measure.infinitePi (coordinateLaw P)

noncomputable def baseMeasure : Measure Endpoint :=
  Measure.infinitePi (fun _ : ℕ => baseLaw)

def hybridEndpoint (ε : ℕ → Bool) (ω : Sample) (i : ℕ) : ℝ :=
  if ε i then rightEndpoint ω i else leftEndpoint ω i

noncomputable def marginalDensity (P : Parameters) (side : Bool) (i : ℕ) : ℝ → ℝ :=
  if side then rightMarginalDensity (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i)
  else leftMarginalDensity (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i)

noncomputable def energyBound (P : Parameters) (i : ℕ) : ℝ :=
  20 * (2 * (P.κ i) ^ 2 / P.m i + P.t i / P.m i)

end Invariant233.OrderedProductCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_ProductCouplingCircle
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.OrderedProductCoupling

def realEndpoint (x : ProductModel.Base) : Endpoint :=
  fun i => circleRepresentative (x i)

def circleHybridEndpoint (ε : ℕ → Bool) : Sample → ProductModel.Base :=
  circleEndpoint ∘ hybridEndpoint ε

def circlePairLaw (P : Parameters) : Measure (ProductModel.Base × ProductModel.Base) :=
  (law P).map (fun ω => (circleLeftEndpoint ω, circleRightEndpoint ω))

end Invariant233.OrderedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_SourceProductTail
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace Invariant233.OrderedProductCoupling

def SourceTailEstimate (p : ProductScaleData) (e : ℕ ≃ Σ s, Fin (p.m s))
    (θ : ℕ → ℝ) (j : ℕ) (P : Parameters) : Prop :=
    ∃ H₁ H₂ : ℤ → Set Sample,
      (∀ k, MeasurableSet (H₁ k)) ∧ (∀ k, MeasurableSet (H₂ k)) ∧
      (∀ᵐ ω ∂law P, ∀ k : ℤ, (p.K j : ℝ) < |(k : ℝ)| →
        ((law P)[(H₁ k).indicator (fun _ => (1 : ℝ)) |
          MeasurableSpace.comap circleLeftEndpoint inferInstance]) ω ≤
            Real.exp (-p.L j / 400) ∧
        ((law P)[(H₂ k).indicator (fun _ => (1 : ℝ)) |
          MeasurableSpace.comap circleRightEndpoint inferInstance]) ω ≤
            Real.exp (-p.L j / 400) ∧
        ((∃ i ∈ ProductPhases.consecutiveBlock p.m j,
          circleRepresentative (circleLeftEndpoint ω i) < 1 / (p.m j : ℝ) ∧
          1 - 1 / (p.m j : ℝ) ≤ circleRepresentative (circleRightEndpoint ω i)) →
          ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) k (circleRightEndpoint ω) /
            ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) k (circleLeftEndpoint ω) ≤
            Real.exp (-p.L j) + (H₁ k).indicator (fun _ => (1 : ℝ)) ω +
              (H₂ k).indicator (fun _ => (1 : ℝ)) ω))

end Invariant233.OrderedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductScaleConstruction
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Invariant233.ProductScaleConstruction

open SamplingHorizon FiniteWindow

structure Step (n : ℕ) (s : State) where
  m : ℕ
  Gnext : ℕ
  L : ℝ
  ε : ℝ
  epsilon_pos : 0 < ε
  L_one : 1 ≤ L
  L_previous : s.previousL ≤ L
  gain_one : 1 ≤ Gnext
  gain : L ≤ ProductScaleData.kappa (n + 1) * Real.sqrt (Gnext : ℝ)
  m_K : s.K ≤ m
  m_pow : 2 ^ (n + 1) ≤ m
  m_G : 4 * s.G ≤ m
  m_large : 200 ≤ m
  count_bound : (s.count : ℝ) ≤ (m : ℝ) / 100
  attenuation_m : L ≤ ProductScaleData.kappa n * (m : ℝ) ^ (1 / 40 : ℝ)
  gap : (Gnext : ℝ) * (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) <
    (m : ℝ) ^ ((4 / 5 : ℝ) * m)
  double : 2 * s.K < ⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊
  attenuation : ((2 * s.K + 1 : ℕ) : ℝ) * 3 * Real.exp (-L / 10000) ≤
    ε / ((n + 1 : ℕ) : ℝ)
  polynomial : ∀ A B : ℤ → ℂ,
    (∀ i, |i| ≤ (s.K : ℤ) → ‖A i‖ ≤ Real.exp (((s.K : ℝ) + 1) * s.cost)) →
    (∀ i, |i| ≤ (s.K : ℤ) → ‖B i‖ ≤ Real.exp (((s.K : ℝ) + 1) * s.cost)) →
    1 / ((n + 1 : ℕ) : ℝ) ≤ ‖A 0‖ → 1 / ((n + 1 : ℕ) : ℝ) ≤ ‖B 0‖ →
    ∃ i : ℕ, i ≤ 2 * s.K ∧ ε ≤ ‖convolution s.K A B i‖

theorem step_exists (n : ℕ) (s : State) : Nonempty (Step n s) := by
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  obtain ⟨ε, hε, hpoly⟩ := uniform_convolution_lower_bound s.K
    (Real.exp (((s.K : ℝ) + 1) * s.cost)) (1 / ((n + 1 : ℕ) : ℝ)) (by positivity)
  obtain ⟨L, hL1, hLprev, hL⟩ := exists_attenuation
    (((2 * s.K + 1 : ℕ) : ℝ) * 3) s.previousL
      (ε / ((n + 1 : ℕ) : ℝ)) (div_pos hε hn)
  have hk : 0 < ProductScaleData.kappa (n + 1) := by
    unfold ProductScaleData.kappa
    positivity
  obtain ⟨G, hG, hgain⟩ := exists_next_gain (ProductScaleData.kappa (n + 1)) L hk
  obtain ⟨m, hmK, hmpow, hmG, hmlarge, hcount, hmL, hgap, _hheight, hdouble⟩ :=
    exists_stage_size (n + 1) (by omega) s.K s.G G L 0 s.count
  exact ⟨{
    m := m, Gnext := G, L := L, ε := ε
    epsilon_pos := hε, L_one := hL1, L_previous := hLprev
    gain_one := hG, gain := hgain
    m_K := by exact_mod_cast hmK
    m_pow := by exact_mod_cast hmpow
    m_G := by exact_mod_cast hmG
    m_large := hmlarge
    count_bound := hcount
    attenuation_m := hmL
    gap := hgap
    double := by exact_mod_cast hdouble
    attenuation := hL
    polynomial := hpoly }⟩

def chooseStep (n : ℕ) (s : State) : Step n s :=
  Classical.choice (step_exists n s)

def nextState (n : ℕ) (s : State) : State :=
  let t := chooseStep n s
  { K := ⌈(t.m : ℝ) ^ ((3 / 4 : ℝ) * t.m)⌉₊
    G := t.Gnext
    count := s.count + t.m
    cost := s.cost + max t.L ((s.K : ℝ) ^ 2) * t.m
    previousL := t.L }

def states : ℕ → State :=
  Nat.rec ⟨100, 1, 0, 0, 0⟩ nextState

def choices (n : ℕ) : Step n (states n) := chooseStep n (states n)

def constructed : ProductScaleData where
  m n := (choices n).m
  K n := (states n).K
  G n := (states n).G
  L n := (choices n).L
  C n := max (choices n).L (((states n).K : ℝ) ^ 2)
  ε n := (choices n).ε

end Invariant233.ProductScaleConstruction

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_OneCoordinateConditional
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.baseLaw_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Invariant233.OneCoordinateCoupling
open CouplingMarginalBounds FiniteKernelMixture

noncomputable def rightGivenLeft (κ m a b t : ℝ) : Kernel ℝ ℝ :=
  diagonalReplacementKernel (ENNReal.ofReal (diagonalMass κ m a b t))
    (fun i => ENNReal.ofReal (componentProbabilities κ m a b t i))
    (fun i x => ENNReal.ofReal (leftDensity m a b i x))
    (fun i => by fin_cases i <;>
      exact (measurable_const.indicator measurableSet_Ico).ennreal_ofReal)
    (rightLaw m a b)

noncomputable def leftGivenRight (κ m a b t : ℝ) : Kernel ℝ ℝ :=
  diagonalReplacementKernel (ENNReal.ofReal (diagonalMass κ m a b t))
    (fun i => ENNReal.ofReal (componentProbabilities κ m a b t i))
    (fun i x => ENNReal.ofReal (rightDensity m a b i x))
    (fun i => by fin_cases i <;>
      exact (measurable_const.indicator measurableSet_Ico).ennreal_ofReal)
    (leftLaw m a b)

end Invariant233.OneCoordinateCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductCoupling
attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

namespace Invariant233.OrderedProductCoupling

open OneCoordinateCoupling

instance coordinateLaw_isProbabilityMeasure (P : Parameters) (i : ℕ) :
    IsProbabilityMeasure (coordinateLaw P i) :=
  labelledLaw_isProbabilityMeasure (P.κ_nonneg i) (P.κ_le i) (P.m_ge i)
    (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i) (P.t_nonneg i) (P.t_le i)

instance law_isProbabilityMeasure (P : Parameters) : IsProbabilityMeasure (law P) := by
  unfold law
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance baseMeasure_isProbabilityMeasure : IsProbabilityMeasure baseMeasure := by
  unfold baseMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma leftEndpoint_measurable : Measurable leftEndpoint := by
  unfold leftEndpoint
  fun_prop

lemma rightEndpoint_measurable : Measurable rightEndpoint := by
  unfold rightEndpoint
  fun_prop

end Invariant233.OrderedProductCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_BlockProductCoupling
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233.OrderedProductCoupling

def ofBlocks (m : ℕ → ℕ) (κ a b : ℕ → ℝ)
    (hκ0 : ∀ s, 0 ≤ κ s) (hκ : ∀ s, κ s ≤ 1 / 100)
    (hm : ∀ s, 100 ≤ m s)
    (ha : ∀ s, 1 / (m s : ℝ) ≤ a s) (ha' : ∀ s, a s ≤ 1 / 4)
    (hb : ∀ s, 1 / (m s : ℝ) ≤ b s) (hb' : ∀ s, b s ≤ 1 / 4)
    (e : ℕ ≃ Σ s, Fin (m s)) (tag : ℕ) : Parameters where
  κ i := κ (e i).1
  m i := m (e i).1
  a i := a (e i).1
  b i := b (e i).1
  t i := if (e i).1 = tag then 1 else 0
  κ_nonneg i := hκ0 (e i).1
  κ_le i := hκ (e i).1
  m_ge i := by exact_mod_cast hm (e i).1
  a_lower i := ha (e i).1
  a_upper i := ha' (e i).1
  b_lower i := hb (e i).1
  b_upper i := hb' (e i).1
  t_nonneg i := by split_ifs <;> norm_num
  t_le i := by split_ifs <;> norm_num

end Invariant233.OrderedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductCouplingCircle
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace Invariant233.OrderedProductCoupling

open OneCoordinateCoupling

lemma circleEndpoint_measurable : Measurable circleEndpoint := by
  unfold circleEndpoint
  fun_prop

lemma circleLeftEndpoint_measurable : Measurable circleLeftEndpoint :=
  circleEndpoint_measurable.comp leftEndpoint_measurable

lemma circleRightEndpoint_measurable : Measurable circleRightEndpoint :=
  circleEndpoint_measurable.comp rightEndpoint_measurable

instance circlePairLaw_probability (P : Parameters) : IsProbabilityMeasure (circlePairLaw P) := by
  unfold circlePairLaw
  exact Measure.isProbabilityMeasure_map (circleLeftEndpoint_measurable.prodMk circleRightEndpoint_measurable).aemeasurable

end Invariant233.OrderedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_SourceCouplingMarginals
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace Invariant233.OrderedProductCoupling

def sourceBlocks (m : ℕ → ℕ) (a b : ℕ → ℝ) (hm : ∀ s, 100 ≤ m s)
    (ha : ∀ s, 1 / (m s : ℝ) ≤ a s) (ha' : ∀ s, a s ≤ 1 / 4)
    (hb : ∀ s, 1 / (m s : ℝ) ≤ b s) (hb' : ∀ s, b s ≤ 1 / 4)
    (e : ℕ ≃ Σ s, Fin (m s)) (tag : ℕ) : Parameters :=
  ofBlocks m sourceKappa a b
    (by intro s; unfold sourceKappa; positivity)
    (by
      intro s
      unfold sourceKappa
      apply (div_le_iff₀ (by positivity : 0 < 100 * ((s : ℝ) + 1))).2
      nlinarith [Nat.cast_nonneg (α := ℝ) s])
    hm ha ha' hb hb' e tag

end Invariant233.OrderedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductConditionalData
attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
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

def sourceLeftVector (F : Base → Fiber →L[ℂ] Fiber) (ω : Sample) : Fiber :=
  F (circleLeftEndpoint ω) sourceUnitVector

def sourceRightVector (F : Base → Fiber →L[ℂ] Fiber) (ω : Sample) : Fiber :=
  (1 - F (circleRightEndpoint ω)) sourceUnitVector

def sourceLeftCocycle (θ c : ℕ → ℝ) (ω : Sample) (k : ℤ) : ℝ :=
  ProductCocycle.cocycleVersion θ c k (circleLeftEndpoint ω)

def sourceRightCocycle (θ c : ℕ → ℝ) (ω : Sample) (k : ℤ) : ℝ :=
  ProductCocycle.cocycleVersion θ c k (circleRightEndpoint ω)

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductScaleCocycleWindow
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate lp

namespace Invariant233.ProductScaleData

def earlyCoordinates (p : ProductScaleData) (e : ℕ ≃ Σ s, Fin (p.m s))
    (j : ℕ) : Finset ℕ :=
  ((Finset.range j).sigma (fun s => (Finset.univ : Finset (Fin (p.m s))))).map
    e.symm.toEmbedding

@[simp] theorem mem_earlyCoordinates (p : ProductScaleData)
    (e : ℕ ≃ Σ s, Fin (p.m s)) (j i : ℕ) :
    i ∈ p.earlyCoordinates e j ↔ (e i).1 < j := by
  simp [earlyCoordinates]

end Invariant233.ProductScaleData

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_MixedRadix
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.MixedRadix

noncomputable def tailValue {r : ℕ → ℕ} (d : Digits r) (j : ℕ) : ℝ :=
  (denominator r j : ℝ) * ∑' n, term d (j + n)

def Nonterminal {r : ℕ → ℕ} (d : Digits r) : Prop :=
  ∀ j, ∃ n, j ≤ n ∧ (d n : ℕ) + 1 < r n

noncomputable def canonicalDigits (r : ℕ → ℕ) (hr : ∀ n, 0 < r n) (x : ℝ) : Digits r :=
  fun n => ⟨⌊(denominator r (n + 1) : ℝ) * x⌋₊ % r n, Nat.mod_lt _ (hr n)⟩

def extendPrefix (r : ℕ → ℕ) (hr : ∀ n, 0 < r n) (N : ℕ)
    (d : (i : Fin N) → Fin (r i)) : Digits r :=
  fun n => if h : n < N then d ⟨n, h⟩ else ⟨0, hr n⟩

end Invariant233.MixedRadix

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_MixedRadixCircle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.MixedRadix

noncomputable def circleCanonical (r : ℕ → ℕ) (hr : ∀ n, 0 < r n)
    (x : AddCircle (1 : ℝ)) : Digits r :=
  canonicalDigits r hr (AddCircle.equivIco (1 : ℝ) 0 x : ℝ)

end Invariant233.MixedRadix

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_MixedRadix
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.MixedRadix.hybrid_apply_ge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Invariant233.MixedRadix

theorem prefixRank_lt_denominator {r : ℕ → ℕ} (_hr : ∀ n, 0 < r n)
    (d : Digits r) (N : ℕ) : prefixRank d N < denominator r N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [prefixRank_succ, denominator_succ]
      have hd := (d N).isLt
      nlinarith [_hr N]

theorem prefixRank_canonicalDigits {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    {x : ℝ} (hx : x ∈ Set.Ico 0 1) (N : ℕ) :
    prefixRank (canonicalDigits r hr x) N = ⌊(denominator r N : ℝ) * x⌋₊ := by
  induction N with
  | zero => simp [Nat.floor_eq_zero.mpr hx.2]
  | succ N ih =>
      rw [prefixRank_succ, ih]
      change ⌊(denominator r N : ℝ) * x⌋₊ * r N +
        ⌊(denominator r (N + 1) : ℝ) * x⌋₊ % r N = _
      have hdiv : ⌊(denominator r (N + 1) : ℝ) * x⌋₊ / r N =
          ⌊(denominator r N : ℝ) * x⌋₊ := by
        rw [denominator_succ, Nat.cast_mul, mul_right_comm, mul_comm _ (r N : ℝ)]
        exact Nat.cast_mul_floor_div_cancel (ne_of_gt (hr N)) _
      rw [← hdiv]
      exact Nat.div_add_mod' _ _

theorem prefixRank_congr {r : ℕ → ℕ} {d e : Digits r} (N : ℕ)
    (hde : ∀ n < N, d n = e n) : prefixRank d N = prefixRank e N := by
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [prefixRank_succ, prefixRank_succ, ih (fun n hn => hde n (by omega)), hde N (by omega)]

theorem prefixRank_eq_iff {r : ℕ → ℕ} (hr : ∀ n, 0 < r n) (d e : Digits r) (N : ℕ) :
    prefixRank d N = prefixRank e N ↔ ∀ n < N, d n = e n := by
  refine ⟨?_, fun h => prefixRank_congr N h⟩
  induction N with
  | zero => intro _ n hn; omega
  | succ N ih =>
      intro heq
      have hlast : d N = e N := by
        apply Fin.ext
        have hmod := congrArg (fun k => k % r N) heq
        simpa [prefixRank_succ, Nat.add_mod, Nat.mul_mod,
          Nat.mod_eq_of_lt (d N).isLt, Nat.mod_eq_of_lt (e N).isLt] using hmod
      have hprev : prefixRank d N = prefixRank e N := by
        rw [prefixRank_succ, prefixRank_succ, hlast] at heq
        exact Nat.eq_of_mul_eq_mul_right (hr N) (Nat.add_right_cancel heq)
      intro n hn
      by_cases hn' : n < N
      · exact ih hprev n hn'
      · have : n = N := by omega
        subst n
        exact hlast

@[simp] theorem extendPrefix_apply_lt {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    {N : ℕ} (d : (i : Fin N) → Fin (r i)) {n : ℕ} (hn : n < N) :
    extendPrefix r hr N d n = d ⟨n, hn⟩ := by
  simp [extendPrefix, hn]

theorem finitePrefixRank_injective {r : ℕ → ℕ} (hr : ∀ n, 0 < r n) (N : ℕ) :
    Function.Injective (fun d : (i : Fin N) → Fin (r i) =>
      prefixRank (extendPrefix r hr N d) N) := by
  intro d e hde
  have h := (prefixRank_eq_iff hr (extendPrefix r hr N d) (extendPrefix r hr N e) N).mp hde
  funext i
  simpa using h i i.isLt

theorem finitePrefixRank_surjective {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (N k : ℕ) (hk : k < denominator r N) :
    ∃ d : (i : Fin N) → Fin (r i), prefixRank (extendPrefix r hr N d) N = k := by
  let x : ℝ := (k : ℝ) / (denominator r N : ℝ)
  have hq : (0 : ℝ) < denominator r N := by exact_mod_cast denominator_pos hr N
  have hx : x ∈ Set.Ico 0 1 := by
    constructor
    · dsimp [x] <;> positivity
    · apply (div_lt_one hq).mpr
      exact_mod_cast hk
  let d := canonicalDigits r hr x
  refine ⟨fun i => d i, ?_⟩
  calc
    prefixRank (extendPrefix r hr N (fun i => d i)) N = prefixRank d N := by
      apply prefixRank_congr
      intro n hn
      simp [hn]
    _ = ⌊(denominator r N : ℝ) * x⌋₊ := prefixRank_canonicalDigits hr hx N
    _ = k := by
      have hscale : (denominator r N : ℝ) * x = (k : ℝ) := by dsimp [x]; field_simp
      rw [hscale, Nat.floor_natCast]

noncomputable def finitePrefixRankEquiv (r : ℕ → ℕ) (hr : ∀ n, 0 < r n) (N : ℕ) :
    ((i : Fin N) → Fin (r i)) ≃ Fin (denominator r N) :=
  Equiv.ofBijective
    (fun d => ⟨prefixRank (extendPrefix r hr N d) N,
      prefixRank_lt_denominator hr (extendPrefix r hr N d) N⟩)
    ⟨fun _ _ h => finitePrefixRank_injective hr N (congrArg Fin.val h),
      fun k => by
        obtain ⟨d, hd⟩ := finitePrefixRank_surjective hr N k k.isLt
        exact ⟨d, Fin.ext hd⟩⟩

@[simp] theorem finitePrefixRankEquiv_val (r : ℕ → ℕ) (hr : ∀ n, 0 < r n)
    (N : ℕ) (d : (i : Fin N) → Fin (r i)) :
    (finitePrefixRankEquiv r hr N d : ℕ) = prefixRank (extendPrefix r hr N d) N := rfl

end Invariant233.MixedRadix

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductSourceConditionalData
attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Invariant233.ProductModel
open OrderedProductCoupling
open InvariantProjection.ConditionalConvolution

abbrev actualSourceParameters {p : ProductScaleData} (hp : ProductScaleLaws p)
    (e : ℕ ≃ Σ s, Fin (p.m s)) (j : ℕ) : Parameters :=
  sourceBlocks p.m p.a p.b hp.m_ge_100
    (fun s => (hp.a_bounds s).1) (fun s => (hp.a_bounds s).2)
    (fun s => (hp.b_bounds s).1) (fun s => (hp.b_bounds s).2) e j

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_DiagonalGauge
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.DiagonalGauge

def fieldOperator {X : Type*} [MeasurableSpace X] (μ : Measure X) (t : Circle) :
    Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ :=
  (fiberOperator t).compLpL 2 μ

def conjugate {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (A : Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ) (t : Circle) :
    Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ :=
  fieldOperator μ t * A * fieldOperator μ (-t)

end Invariant233.DiagonalGauge

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_MixedRadixProbability
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Invariant233.MixedRadix

def digitLaw (r : ℕ → ℕ) (hr : ∀ n, 0 < r n) : Measure (Digits r) := by
  letI : ∀ n, NeZero (r n) := fun n => ⟨ne_of_gt (hr n)⟩
  exact Measure.infinitePi (fun n => (PMF.uniformOfFintype (Fin (r n))).toMeasure)

end Invariant233.MixedRadix

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_PrefixDomination
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.baseLaw_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Invariant233.OneCoordinateCoupling

def triangleLaw : Measure (ℝ × ℝ) :=
  (baseLaw.prod baseLaw).restrict {z | z.1 < z.2}

def replacementDensity (m a b : ℝ) (i : Fin 5) (z : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (leftDensity m a b i z.1) *
    ENNReal.ofReal (rightDensity m a b i z.2)

end Invariant233.OneCoordinateCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_ProductPrefixDomination
attribute [-instance] _root_.OAI.Invariant233.CouplingMixture.diagonal_isProbabilityMeasure _root_.OAI.Invariant233.OneCoordinateCoupling.baseLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.baseMeasure_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace Invariant233.OrderedProductCoupling

def assemblePrefixPair (D : ℕ) (z : PrefixPairs D × TailValues D) : Endpoint × Endpoint :=
  ((fun i => if hi : i ∈ Finset.range D then (z.1 ⟨i, hi⟩).1 else z.2 ⟨i, hi⟩),
   (fun i => if hi : i ∈ Finset.range D then (z.1 ⟨i, hi⟩).2 else z.2 ⟨i, hi⟩))

def prefixPairLaw (P : Parameters) (D : ℕ) : Measure (Endpoint × Endpoint) :=
  (law P).map (fun ω => (leftEndpoint ω,
    hybridEndpoint (fun i => decide (i ∈ Finset.range D)) ω))

def prefixPairsLaw (P : Parameters) (D : ℕ) : Measure (PrefixPairs D) :=
  Measure.pi (fun i => OneCoordinateCoupling.pairLaw
    (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i))

def leftTailLaw (P : Parameters) (D : ℕ) : Measure (TailValues D) :=
  Measure.infinitePi (fun i : TailIndex D =>
    (coordinateLaw P i).map (fun z => z.2.1))

def baseTailLaw (D : ℕ) : Measure (TailValues D) :=
  Measure.infinitePi (fun _ => OneCoordinateCoupling.baseLaw)

def prefixReferenceLaw (D : ℕ) : Measure (PrefixPairs D) :=
  ∑ pattern : PrefixIndex D → Bool, Measure.pi (fun i =>
    if pattern i then OneCoordinateCoupling.triangleLaw
    else CouplingMixture.diagonal OneCoordinateCoupling.baseLaw)

def prefixReferencePairLaw (D : ℕ) : Measure (Endpoint × Endpoint) :=
  ((prefixReferenceLaw D).prod (baseTailLaw D)).map (assemblePrefixPair D)

end Invariant233.OrderedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_ProductScaleSampling
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233

structure ProductSamplingPowersAt (p : ProductScaleData) (j : ℕ)
    (s : Finset ℕ) : Prop where
  range : ∀ n ∈ s, (p.m j : ℝ) ^ ((7 / 10 : ℝ) * p.m j) / 2 ≤ n ∧
    (n : ℝ) ≤ (p.m j : ℝ) ^ ((7 / 10 : ℝ) * p.m j)
  cardinality : (p.m j : ℝ) ^ ((69 / 100 : ℝ) * p.m j) ≤ (s.card : ℝ)
  positive : ∀ n ∈ s, 0 < n
  separation : ∀ n ∈ s, ∀ n' ∈ s, n ≠ n' → ∀ v v' : ℤ,
    |v| ≤ (p.m j ^ 300 : ℕ) → |v'| ≤ (p.m j ^ 300 : ℕ) →
    (v ≠ 0 ∨ v' ≠ 0) →
    (p.m j * p.K j * p.m j ^ 1000 : ℕ) < |v * (n : ℤ) + v' * (n' : ℤ)|

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_RealTriangularLaw
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.baseMeasure_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.OrderedProductCoupling

def realSelectedEndpoint (I : Finset ℕ) (x z : Endpoint) : Endpoint :=
  fun i => if i ∈ I then z i else x i

def realTriangularEvent (I : Finset ℕ) : Set (Endpoint × Endpoint) :=
  {xz | ∀ i ∈ I, xz.1 i < xz.2 i}

def realTriangularLaw (I : Finset ℕ) : Measure (Endpoint × Endpoint) :=
  ((baseMeasure.prod baseMeasure).restrict (realTriangularEvent I)).map
    (fun xz => (xz.1, realSelectedEndpoint I xz.1 xz.2))

def circlePairEndpoint : Endpoint × Endpoint → ProductModel.EndpointPair :=
  Prod.map circleEndpoint circleEndpoint

end Invariant233.OrderedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_SamplingTests
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Invariant233.SamplingTests

def kernel (endpoint : Bool) (m : ℕ) (z v : ℝ) : ℝ :=
  CircleParameterData.orientedKernel endpoint m z (Int.fract v)

def circleKernel (endpoint : Bool) (m : ℕ) (v : ℝ) (x : Circle) : ℝ :=
  kernel endpoint m (CircleParameterData.rep x) v

def average (endpoint : Bool) (m d : ℕ) (s : Finset ℕ)
    (z : (Fin d → ℝ) × UnitAddTorus (Fin d)) : ℝ :=
  ((s.card : ℝ)⁻¹) * ∑ n ∈ s, ∏ i : Fin d,
    circleKernel endpoint m ((n : ℝ) * z.1 i) (z.2 i)

def errorSq (endpoint : Bool) (m d : ℕ) (s : Finset ℕ)
    (z : (Fin d → ℝ) × UnitAddTorus (Fin d)) : ℝ :=
  (average endpoint m d s z - 1) ^ 2

end Invariant233.SamplingTests

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_SawtoothSmoothing
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace InvariantProjection.Continuity

def smoothingTransfer (C δ u : ℝ) : ℝ :=
  C * (smoothSawtooth δ u - Int.fract u)

end InvariantProjection.Continuity

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_StrictPhase
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.ProductPhases

noncomputable def strictLargePhaseFailure {ι : Type*} (J : Finset ι) (N : ℝ) :
    Set (ι → ℝ) :=
  {θ | ∃ k ∈ largePhaseTimes N ((J.card : ℝ) ^ ((4 / 5 : ℝ) * J.card)),
    (strictPhaseGoodCount J ((J.card : ℝ) ^ (-19 / 20 : ℝ)) k θ : ℝ) <
      (J.card : ℝ) / 20}

end Invariant233.ProductPhases

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Model_TrialSampling
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace Invariant233.TrialSampling

def squaredError (m : ℕ) (samples : Finset ℕ) (endpoint : Bool)
    (phase : Fin m → ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal ((average m samples endpoint phase z - 1) ^ 2) ∂spatialLaw m

def coordinateSample (m : ℕ) (endpoint : Bool) (n : ℕ) (p : ℝ × Circle) : ℝ :=
  CircleParameterData.orientedKernel endpoint m (CircleParameterData.rep p.2)
    (Int.fract ((n : ℝ) * p.1))

def coordinateIdeal (m : ℕ) (endpoint : Bool) (p : ℝ × Circle) : ℝ :=
  ∫ v, CircleParameterData.orientedKernel endpoint m (CircleParameterData.rep p.2) v
    ∂volume.restrict (Set.Ioc (0 : ℝ) 1)

end Invariant233.TrialSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_VectorTraceState
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.ConcretePredual.evaluationLinearIsometryEquiv_apply _root_.OAI.Invariant233.ConcretePredual.evaluationLinearIsometry_apply _root_.OAI.Invariant233.ConcretePredual.evaluation_apply _root_.OAI.Invariant233.ConcretePredual.evaluation_vector _root_.OAI.Invariant233.ConcretePredual.inner_representingOperator _root_.OAI.Invariant233.ConcretePredual.norm_evaluation _root_.OAI.Invariant233.ConcretePredual.vectorFunctional_add_left _root_.OAI.Invariant233.ConcretePredual.vectorFunctional_add_right _root_.OAI.Invariant233.ConcretePredual.vectorFunctional_apply _root_.OAI.Invariant233.ConcretePredual.vectorFunctional_smul_left _root_.OAI.Invariant233.ConcretePredual.vectorFunctional_smul_right _root_.OAI.Invariant233.ConcretePredual.vector_coe _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProjectionMeetTrace.vectorFunctional_apply _root_.OAI.Invariant233.vectorTraceContinuousLinearMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

@[simp]
theorem vonNeumannVectorTraceCLM_apply (M : VonNeumannAlgebra H) (ξ : H) (A : M) :
    vonNeumannVectorTraceCLM M ξ A = vectorTrace ξ (A : H →L[ℂ] H) := rfl

@[simp]
theorem IsFaithfulTracialVector.toTracialState_apply {M : VonNeumannAlgebra H} {ξ : H}
    (h : IsFaithfulTracialVector M ξ) (A : M) :
    h.toTracialState A = vectorTrace ξ (A : H →L[ℂ] H) := rfl

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CirclePhaseSummability
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233
open scoped BigOperators ENNReal

namespace CircleParameterLaws
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

def blocksWithZero (p : CircleParameterData) (j : ℕ) : Finset ℕ :=
  if j = 0 then {0} else p.block j

end CircleParameterLaws
end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_RotationTransfer
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace Invariant233.Rotation

theorem exponentialTransfer_coefficient_measurable (θ : ℝ) {b : Circle → ℝ}
    (hb : Measurable b) (k : ℤ) :
    Measurable (fun x => Real.exp (b (action θ k x))) :=
  (hb.comp (action_continuous θ k).measurable).exp

end Invariant233.Rotation

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_RotationTransferIntertwining
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace Invariant233.Rotation

theorem ae_all_action_factor (θ : ℝ) (b : Circle → ℝ) (f g : Circle → ℂ) (c : ℂ)
    (hfactor : ∀ᵐ x ∂circleMeasure,
      (Real.exp (b (x + (θ : Circle))) : ℂ) * f x =
        c * g x * (Real.exp (b x) : ℂ)) :
    ∀ᵐ x ∂circleMeasure, ∀ k : ℤ,
      (Real.exp (b (action θ (k + 1) x)) : ℂ) * f (action θ k x) =
        c * g (action θ k x) * (Real.exp (b (action θ k x)) : ℂ) := by
  apply ae_all_iff.mpr
  intro k
  have h := (action_measurePreserving θ k).quasiMeasurePreserving.ae hfactor
  filter_upwards [h] with x hx
  have hstep : action θ k x + (θ : Circle) = action θ (k + 1) x := by
    simp only [action, add_zsmul, one_zsmul]
    abel
  simpa only [hstep] using hx

theorem weightedReal_mem_exponentialTransfer_domain
    (θ : ℝ) (b : Circle → ℝ) (f : C(Circle, ℝ))
    (g : Circle → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) (c : ℂ)
    (hfactor : ∀ᵐ x ∂circleMeasure,
      (Real.exp (b (x + (θ : Circle))) : ℂ) * (f x : ℂ) =
        c * g x * (Real.exp (b x) : ℂ))
    (ξ : (exponentialTransfer θ b).domain) :
    weightedReal θ f ξ.val ∈ (exponentialTransfer θ b).domain := by
  apply WeightedShift.field_operator_mem_multiplierDomain
    (fun x k => (Real.exp (b (action θ k x)) : ℂ))
    (fun x k => ((f (action θ k x)) : ℂ))
    (fun x k => g (action θ k x)) c
    (weightedReal θ f) (U * measurableRepresentation θ g C hC hg hb)
  · exact weighted_coordinates_ae θ (complexWeight f)
  · exact U_mul_measurableRepresentation_coordinates_ae θ g C hC hg hb
  · exact ae_all_action_factor θ b (fun x => (f x : ℂ)) g c hfactor

end Invariant233.Rotation

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_WeightedShiftPolar
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.WeightedShift.diagonalAlgHom_apply _root_.OAI.Invariant233.WeightedShift.diagonal_add _root_.OAI.Invariant233.WeightedShift.diagonal_mul _root_.OAI.Invariant233.WeightedShift.diagonal_one _root_.OAI.Invariant233.WeightedShift.diagonal_smul _root_.OAI.Invariant233.WeightedShift.diagonal_star _root_.OAI.Invariant233.WeightedShift.diagonal_zero _root_.OAI.Invariant233.WeightedShift.translate_add _root_.OAI.Invariant233.WeightedShift.translate_apply _root_.OAI.Invariant233.WeightedShift.translate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal InnerProductSpace ComplexOrder
namespace Invariant233.WeightedShift.PolarSupport

def sqrtRealWeight (w : Weight) : Weight :=
  ⟨fun k => (Real.sqrt (w k).re : ℂ), memℓp_infty <| by
    refine ⟨Real.sqrt ‖w‖, ?_⟩
    rintro r ⟨k, rfl⟩
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt ((Complex.re_le_norm _).trans
      (lp.norm_apply_le_norm (by simp) w k))⟩

end Invariant233.WeightedShift.PolarSupport

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_FieldDiagonalPolar
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal InnerProductSpace ComplexOrder
namespace Invariant233.WeightedShift
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

local instance fieldDiagonalPolarRealModule : Module ℝ
    (Lp Hilbert 2 μ →L[ℂ] Lp Hilbert 2 μ) :=
  Module.complexToReal (Lp Hilbert 2 μ →L[ℂ] Lp Hilbert 2 μ)

local instance fieldDiagonalPolarFunctionalCalculus : NonUnitalContinuousFunctionalCalculus ℝ
    (Lp Hilbert 2 μ →L[ℂ] Lp Hilbert 2 μ) IsSelfAdjoint := by
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_FieldResolvent
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
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

def positiveResolventWeight (h : X → ℤ → ℝ) (hpos : ∀ x k, 0 ≤ h x k)
    (x : X) : Weight :=
  ⟨fun k => (((1 + h x k)⁻¹ : ℝ) : ℂ), memℓp_infty <| by
    refine ⟨1, ?_⟩
    rintro r ⟨k, rfl⟩
    simpa only [Complex.norm_real] using
      resolventCoefficient_bound (h x k) (hpos x k)⟩

omit [MeasurableSpace X] in
theorem positiveResolventWeight_bound
    (h : X → ℤ → ℝ) (hpos : ∀ x k, 0 ≤ h x k) (x : X) :
    ‖positiveResolventWeight h hpos x‖ ≤ 1 := by
  apply lp.norm_le_of_forall_le (by norm_num)
  intro k
  simpa only [positiveResolventWeight, Complex.norm_real] using
    resolventCoefficient_bound (h x k) (hpos x k)

theorem positiveResolventWeight_measurable
    (h : X → ℤ → ℝ) (hpos : ∀ x k, 0 ≤ h x k)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) (k : ℤ) :
    AEStronglyMeasurable (fun x => positiveResolventWeight h hpos x k) μ :=
  Complex.continuous_ofReal.comp_aestronglyMeasurable (((hm k).const_add 1).inv₀)

def positiveFieldResolvent (h : X → ℤ → ℝ) (hpos : ∀ x k, 0 ≤ h x k)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) :
    FieldHilbert μ →L[ℂ] FieldHilbert μ :=
  fieldDiagonal (positiveResolventWeight h hpos) 1 (by norm_num)
    (positiveResolventWeight_bound h hpos)
    (positiveResolventWeight_measurable h hpos hm)

theorem positiveFieldResolvent_ae
    (h : X → ℤ → ℝ) (hpos : ∀ x k, 0 ≤ h x k)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) (ξ : FieldHilbert μ) :
    ∀ᵐ x ∂μ, ∀ k,
      positiveFieldResolvent h hpos hm ξ x k =
        (((1 + h x k)⁻¹ : ℝ) : ℂ) * ξ x k :=
  fieldDiagonal_coordinate_ae _ _ _ _ _ ξ

theorem positiveFieldResolvent_mem_domain
    (h : X → ℤ → ℝ) (hpos : ∀ x k, 0 ≤ h x k)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) (ξ : FieldHilbert μ) :
    positiveFieldResolvent h hpos hm ξ ∈
      (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).domain := by
  apply (mem_fieldUnboundedMultiplier_domain_iff _ _).mpr
  refine ⟨ξ - positiveFieldResolvent h hpos hm ξ, ?_⟩
  filter_upwards [positiveFieldResolvent_ae h hpos hm ξ,
    Lp.coeFn_sub ξ (positiveFieldResolvent h hpos hm ξ)] with x hR hsub
  intro k
  rw [hsub]
  change ξ x k - positiveFieldResolvent h hpos hm ξ x k = _
  rw [hR]
  exact resolvent_scalar_identity (h x k) (hpos x k) (ξ x k)

theorem positiveFieldResolvent_apply_add_multiplier
    (h : X → ℤ → ℝ) (hpos : ∀ x k, 0 ≤ h x k)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ)
    (ξ : (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).domain) :
    positiveFieldResolvent h hpos hm
      (ξ.val + fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ)) ξ) = ξ.val := by
  apply fieldHilbert_ext
  filter_upwards [positiveFieldResolvent_ae h hpos hm
      (ξ.val + fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ)) ξ),
    fieldUnboundedMultiplier_apply_ae (fun x k => (h x k : ℂ)) ξ,
    Lp.coeFn_add ξ.val (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ)) ξ)]
    with x hR hH hadd
  intro k
  rw [hR, hadd]
  change (((1 + h x k)⁻¹ : ℝ) : ℂ) *
    (ξ.val x k + fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ)) ξ x k) = _
  rw [hH]
  have hne : (1 + (h x k : ℂ)) ≠ 0 := by
    exact_mod_cast (show (1 + h x k : ℝ) ≠ 0 by
      have := hpos x k
      positivity)
  push_cast
  field_simp

theorem fieldUnboundedMultiplier_domain_eq_resolvent_range
    (h : X → ℤ → ℝ) (hpos : ∀ x k, 0 ≤ h x k)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) :
    (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).domain =
      LinearMap.range (positiveFieldResolvent h hpos hm).toLinearMap := by
  ext ξ
  constructor
  · intro hξ
    exact ⟨ξ + fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ)) ⟨ξ, hξ⟩,
      positiveFieldResolvent_apply_add_multiplier h hpos hm ⟨ξ, hξ⟩⟩
  · rintro ⟨η, rfl⟩
    exact positiveFieldResolvent_mem_domain h hpos hm η

theorem fieldUnboundedMultiplier_domain_invariant_of_commute_resolvent
    (h : X → ℤ → ℝ) (hpos : ∀ x k, 0 ≤ h x k)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ)
    (A : FieldHilbert μ →L[ℂ] FieldHilbert μ)
    (hA : Commute A (positiveFieldResolvent h hpos hm))
    (ξ : (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).domain) :
    A ξ.val ∈ (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).domain := by
  apply (fieldUnboundedMultiplier_domain_eq_resolvent_range h hpos hm).ge
  refine ⟨A (ξ.val + fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ)) ξ), ?_⟩
  have heq := congrArg (fun B : FieldHilbert μ →L[ℂ] FieldHilbert μ =>
    B (ξ.val + fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ)) ξ)) hA.eq
  change positiveFieldResolvent h hpos hm
    (A (ξ.val + fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ)) ξ)) = A ξ.val
  change A (positiveFieldResolvent h hpos hm
    (ξ.val + fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ)) ξ)) =
    positiveFieldResolvent h hpos hm
      (A (ξ.val + fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ)) ξ)) at heq
  rw [← heq, positiveFieldResolvent_apply_add_multiplier h hpos hm ξ]

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_RotationResolvent
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.Rotation

theorem measurable_positive_orbit (θ : ℝ) (h : Circle → ℝ)
    (hm : Measurable h) (k : ℤ) :
    AEStronglyMeasurable (fun x => h (action θ k x)) circleMeasure :=
  (hm.comp (action_measurePreserving θ k).measurable).aestronglyMeasurable

end Invariant233.Rotation

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleMarginalBudget
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Invariant233
namespace CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

def budgetBlocks (p : CircleParameterData) (s : ℕ) : Finset ℕ :=
  if s = 0 then {0} else p.block s

end CircleParameterLaws

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_MixedRadixLaw
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal BigOperators Classical

namespace Invariant233.MixedRadix

instance digitLaw_isProbability (r : ℕ → ℕ) (hr : ∀ n, 0 < r n) :
    IsProbabilityMeasure (digitLaw r hr) := by
  unfold digitLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Invariant233.MixedRadix

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleParameterRecursion
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace Invariant233.CircleParameterRecursion
open PrescribedPhaseRealization SamplingHorizon FiniteWindow

structure Step (θ : ℝ) (height : ℕ → ℕ) (n : ℕ) (s : State) where
  m : ℕ
  Gnext : ℕ
  L : ℝ
  ε : ℝ
  epsilon_pos : 0 < ε
  L_one : 1 ≤ L
  L_previous : s.previousL ≤ L
  gain_one : 1 ≤ Gnext
  gain : L ≤ CircleParameterData.kappa (n + 2) * Real.sqrt (Gnext : ℝ)
  m_K : s.K ≤ m
  m_pow : 2 ^ (n + 1) ≤ m
  m_G : 4 * s.G ≤ m
  m_large : 200 ≤ m
  attenuation_m : L ≤ CircleParameterData.kappa (n + 1) *
    (m : ℝ) ^ (1 / 40 : ℝ)
  gap : (Gnext : ℝ) * (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) <
    (m : ℝ) ^ ((4 / 5 : ℝ) * m)
  continuity : (height (n + 2) : ℝ) /
    (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) ≤ (1 / 2 : ℝ) ^ (n + 1)
  double : 2 * s.K < ⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊
  attenuation : ((2 * s.K + 1 : ℕ) : ℝ) * 3 * Real.exp (-L / 10000) ≤
    ε / ((n + 1 : ℕ) : ℝ)
  polynomial : ∀ A B : ℤ → ℂ,
    (∀ i, |i| ≤ (s.K : ℤ) → ‖A i‖ ≤ Real.exp (((s.K : ℝ) + 1) * s.cost)) →
    (∀ i, |i| ≤ (s.K : ℤ) → ‖B i‖ ≤ Real.exp (((s.K : ℝ) + 1) * s.cost)) →
    1 / ((n + 1 : ℕ) : ℝ) ≤ ‖A 0‖ → 1 / ((n + 1 : ℕ) : ℝ) ≤ ‖B 0‖ →
    ∃ i : ℕ, i ≤ 2 * s.K ∧ ε ≤ ‖convolution s.K A B i‖
  sampling : CircleSamplingStage θ (n + 1) s.K s.d (s.q s.d) m
    (max s.previousN ((m : ℝ) * s.K))

theorem step_exists {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (n : ℕ) (s : State) : Nonempty (Step θ height n s) := by
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  obtain ⟨ε, hε, hpoly⟩ := uniform_convolution_lower_bound s.K
    (Real.exp (((s.K : ℝ) + 1) * s.cost)) (1 / ((n + 1 : ℕ) : ℝ)) (by positivity)
  obtain ⟨L, hL1, hLprev, hL⟩ := exists_attenuation
    (((2 * s.K + 1 : ℕ) : ℝ) * 3) s.previousL
    (ε / ((n + 1 : ℕ) : ℝ)) (div_pos hε hn)
  have hk : 0 < CircleParameterData.kappa (n + 2) := by
    unfold CircleParameterData.kappa
    positivity
  obtain ⟨G, hG, hgain⟩ := exists_next_gain (CircleParameterData.kappa (n + 2)) L hk
  have hnum := eventually_stage_size (n + 1) (by omega) s.K s.G G L
    (height (n + 2)) s.d
  have hsam := hs (n + 1) s.K s.d (s.q s.d) (by omega) s.K_pos (s.q_pos _ le_rfl)
  obtain ⟨m, hm, ht⟩ := (hnum.and hsam).exists
  obtain ⟨hmK, hmpow, hmG, hmlarge, _hcount, hmL, hgap, hheight, hdouble⟩ := hm
  obtain ⟨t⟩ := ht (max s.previousN ((m : ℝ) * s.K))
  exact ⟨{
    m := m, Gnext := G, L := L, ε := ε
    epsilon_pos := hε, L_one := hL1, L_previous := hLprev
    gain_one := hG, gain := hgain
    m_K := by exact_mod_cast hmK
    m_pow := by exact_mod_cast hmpow
    m_G := by exact_mod_cast hmG
    m_large := hmlarge
    attenuation_m := hmL, gap := hgap, continuity := hheight
    double := by exact_mod_cast hdouble
    attenuation := hL, polynomial := hpoly, sampling := t }⟩

def chooseStep {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (n : ℕ) (s : State) : Step θ height n s :=
  Classical.choice (step_exists hs height n s)

def nextState {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (n : ℕ) (s : State) : State := by
  let t := chooseStep hs height n s
  let q := spliceFrequency s.q t.sampling.q s.d
  have hb := t.sampling.q_zero
  exact {
    K := ⌈(t.m : ℝ) ^ ((3 / 4 : ℝ) * t.m)⌉₊
    G := t.Gnext
    d := s.d + t.m
    q := q
    cost := s.cost + max t.L ((s.K : ℝ) ^ 2) * t.m
    previousL := t.L
    previousN := (t.m : ℝ) * s.K
    K_pos := by have := t.double; omega
    G_pos := by have := t.gain_one; omega
    q_zero := (spliceFrequency_eq_old s.q t.sampling.q (Nat.zero_le _)).trans s.q_zero
    q_pos := fun i _ => spliceFrequency_pos s.q t.sampling.q s.d s.q_pos t.sampling.q_pos i
    q_mono := fun i _ => spliceFrequency_strictMono s.q t.sampling.q s.d hb
      s.q_mono t.sampling.q_strict (Nat.lt_succ_self i)
    q_div := fun i _ => spliceFrequency_divisible s.q t.sampling.q s.d hb
      s.q_div t.sampling.q_div i }

def states {θ : ℝ} (hs : CircleStageSupply θ) (height : ℕ → ℕ) : ℕ → State :=
  Nat.rec initial (nextState hs height)

def choices {θ : ℝ} (hs : CircleStageSupply θ) (height : ℕ → ℕ) (n : ℕ) :
    Step θ height n (states hs height n) := chooseStep hs height n (states hs height n)

theorem states_d_succ {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (n : ℕ) :
    (states hs height (n + 1)).d = (states hs height n).d + (choices hs height n).m := rfl

theorem states_d_ge {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (n : ℕ) : n ≤ (states hs height n).d := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    rw [states_d_succ]
    have := (choices hs height n).m_large
    omega

theorem states_d_mono {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) : Monotone (fun n => (states hs height n).d) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [states_d_succ]
  omega

theorem states_keep {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (n i : ℕ) (hi : i ≤ (states hs height n).d) :
    (states hs height (n + 1)).q i = (states hs height n).q i :=
  spliceFrequency_eq_old _ _ hi

theorem exists_global_frequency {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) :
    ∃ Q : ℕ → ℕ,
      (∀ n i, i ≤ (states hs height n).d → Q i = (states hs height n).q i) ∧
      (∀ i, 0 < Q i) ∧ StrictMono Q ∧ (∀ i, Q i ∣ Q (i + 1)) :=
  exists_frequency_of_prefix_tower (fun n => (states hs height n).d)
    (fun n => (states hs height n).q) (states_d_mono hs height)
    (states_d_ge hs height) (states_keep hs height)
    (fun n => (states hs height n).q_pos) (fun n => (states hs height n).q_mono)
    (fun n => (states hs height n).q_div)

def globalFrequency {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) : ℕ → ℕ := Classical.choose (exists_global_frequency hs height)

def constructed {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (φ : ℕ → ℕ → C(Circle, ℝ)) : CircleParameterData where
  m j := (choices hs height (j - 1)).m
  K j := (states hs height (j - 1)).K
  G j := (states hs height (j - 1)).G
  q := globalFrequency hs height
  L j := (choices hs height (j - 1)).L
  C j := max (choices hs height (j - 1)).L (((states hs height (j - 1)).K : ℝ) ^ 2)
  ε j := (choices hs height (j - 1)).ε
  height := height
  partition := φ
  samples j r := if hr : r < (states hs height (j - 1)).q (states hs height (j - 1)).d
    then (choices hs height (j - 1)).sampling.samples ⟨r, hr⟩ else ∅

end Invariant233.CircleParameterRecursion

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_SamplingTestTrialBridge
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Invariant233.SamplingTests

@[simp] lemma average_eq_trialAverage (endpoint : Bool) (m : ℕ) (s : Finset ℕ)
    (τ : Fin m → ℝ) (y : UnitAddTorus (Fin m)) :
    average endpoint m m s (τ,y) = TrialSampling.average m s endpoint τ y := rfl

@[simp] lemma spatialLaw_eq_volume (m : ℕ) :
    TrialSampling.spatialLaw m = (volume : Measure (UnitAddTorus (Fin m))) := rfl

end Invariant233.SamplingTests

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_PrescribedAngleConditional
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The spectral-radius hypothesis and its consequences for prescribed irrational angles. -/

noncomputable section
open Filter
open scoped ENNReal Topology

namespace Invariant233

structure PublishedRotationSpectralInput (θ : ℝ) : Prop where
  radius_zero : ∀ f : C(Circle, ℝ), IsContinuousCircleWeight f →
    spectralRadius ℂ (Rotation.weightedReal θ f) = 0

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductMultiplierFunctionalCalculus
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.ProductModel

theorem multiplier_coordinates_ae (θ : ℕ → ℝ) (g : Base → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) (ξ : Hilbert) :
    ∀ᵐ x ∂baseMeasure, ∀ k : ℤ,
      multiplier θ g C hC hg hb ξ x k = g (rotationIterate θ k x) * ξ x k := by
  unfold multiplier
  exact WeightedShift.fieldDiagonal_coordinate_ae _ _ _ _ _ ξ

theorem multiplier_operator_ext {A B : Hilbert →L[ℂ] Hilbert}
    (h : ∀ ξ : Hilbert, ∀ᵐ x ∂baseMeasure, ∀ k : ℤ, A ξ x k = B ξ x k) :
    A = B := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [h ξ] with x hx
  exact lp.ext (funext hx)

section ContinuousValues
variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]

def continuousValueMultiplier (θ : ℕ → ℝ) (a : Base → Y) (ha : Measurable a)
    (f : C(Y, ℂ)) : Hilbert →L[ℂ] Hilbert :=
  multiplier θ (fun x => f (a x)) ‖f‖ (norm_nonneg f)
    (f.continuous.measurable.comp ha) (fun x => f.norm_coe_le_norm (a x))

theorem continuousValueMultiplier_coordinates_ae (θ : ℕ → ℝ)
    (a : Base → Y) (ha : Measurable a) (f : C(Y, ℂ)) (ξ : Hilbert) :
    ∀ᵐ x ∂baseMeasure, ∀ k : ℤ,
      continuousValueMultiplier θ a ha f ξ x k =
        f (a (rotationIterate θ k x)) * ξ x k :=
  multiplier_coordinates_ae θ _ _ _ _ _ ξ

@[simp] theorem continuousValueMultiplier_one (θ : ℕ → ℝ)
    (a : Base → Y) (ha : Measurable a) :
    continuousValueMultiplier θ a ha 1 = 1 := by
  apply multiplier_operator_ext
  intro ξ
  filter_upwards [continuousValueMultiplier_coordinates_ae θ a ha 1 ξ] with x hx
  intro k
  simpa only [ContinuousMap.one_apply, one_mul, one_apply_eq_self] using hx k

@[simp] theorem continuousValueMultiplier_mul (θ : ℕ → ℝ)
    (a : Base → Y) (ha : Measurable a) (f g : C(Y, ℂ)) :
    continuousValueMultiplier θ a ha (f * g) =
      continuousValueMultiplier θ a ha f * continuousValueMultiplier θ a ha g := by
  apply multiplier_operator_ext
  intro ξ
  filter_upwards [continuousValueMultiplier_coordinates_ae θ a ha (f * g) ξ,
    continuousValueMultiplier_coordinates_ae θ a ha f (continuousValueMultiplier θ a ha g ξ),
    continuousValueMultiplier_coordinates_ae θ a ha g ξ] with x hfg hf hg
  intro k
  change continuousValueMultiplier θ a ha (f * g) ξ x k =
    continuousValueMultiplier θ a ha f (continuousValueMultiplier θ a ha g ξ) x k
  rw [hfg k, hf k, hg k, ContinuousMap.mul_apply, mul_assoc]

@[simp] theorem continuousValueMultiplier_add (θ : ℕ → ℝ)
    (a : Base → Y) (ha : Measurable a) (f g : C(Y, ℂ)) :
    continuousValueMultiplier θ a ha (f + g) =
      continuousValueMultiplier θ a ha f + continuousValueMultiplier θ a ha g := by
  apply multiplier_operator_ext
  intro ξ
  filter_upwards [continuousValueMultiplier_coordinates_ae θ a ha (f + g) ξ,
    continuousValueMultiplier_coordinates_ae θ a ha f ξ,
    continuousValueMultiplier_coordinates_ae θ a ha g ξ,
    Lp.coeFn_add (continuousValueMultiplier θ a ha f ξ)
      (continuousValueMultiplier θ a ha g ξ)] with x hfg hf hg hs
  intro k
  change continuousValueMultiplier θ a ha (f + g) ξ x k =
    ((continuousValueMultiplier θ a ha f ξ + continuousValueMultiplier θ a ha g ξ) x) k
  rw [hs]
  change continuousValueMultiplier θ a ha (f + g) ξ x k =
    continuousValueMultiplier θ a ha f ξ x k + continuousValueMultiplier θ a ha g ξ x k
  rw [hfg k, hf k, hg k, ContinuousMap.add_apply, add_mul]

@[simp] theorem continuousValueMultiplier_smul (θ : ℕ → ℝ)
    (a : Base → Y) (ha : Measurable a) (z : ℂ) (f : C(Y, ℂ)) :
    continuousValueMultiplier θ a ha (z • f) = z • continuousValueMultiplier θ a ha f := by
  apply multiplier_operator_ext
  intro ξ
  filter_upwards [continuousValueMultiplier_coordinates_ae θ a ha (z • f) ξ,
    continuousValueMultiplier_coordinates_ae θ a ha f ξ,
    Lp.coeFn_smul z (continuousValueMultiplier θ a ha f ξ)] with x hzf hf hs
  intro k
  change continuousValueMultiplier θ a ha (z • f) ξ x k =
    ((z • continuousValueMultiplier θ a ha f ξ) x) k
  rw [hs]
  change continuousValueMultiplier θ a ha (z • f) ξ x k =
    z * continuousValueMultiplier θ a ha f ξ x k
  rw [hzf k, hf k]
  simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc]

@[simp] theorem continuousValueMultiplier_star (θ : ℕ → ℝ)
    (a : Base → Y) (ha : Measurable a) (f : C(Y, ℂ)) :
    continuousValueMultiplier θ a ha (star f) = star (continuousValueMultiplier θ a ha f) := by
  unfold continuousValueMultiplier multiplier
  apply WeightedShift.fieldDiagonal_star_of_eq
  exact Filter.Eventually.of_forall fun x => lp.ext (funext fun k => rfl)

@[simp] theorem continuousValueMultiplier_zero (θ : ℕ → ℝ)
    (a : Base → Y) (ha : Measurable a) : continuousValueMultiplier θ a ha 0 = 0 := by
  have h := continuousValueMultiplier_smul θ a ha (0 : ℂ) (1 : C(Y, ℂ))
  apply ContinuousLinearMap.ext
  intro vector
  simpa only [zero_smul, smul_apply, zero_apply]
    using congrArg (fun operator : Hilbert →L[ℂ] Hilbert => operator vector) h

def continuousValueRepresentation (θ : ℕ → ℝ) (a : Base → Y) (ha : Measurable a) :
    C(Y, ℂ) →⋆ₐ[ℂ] (Hilbert →L[ℂ] Hilbert) where
  toFun := continuousValueMultiplier θ a ha
  map_one' := continuousValueMultiplier_one θ a ha
  map_mul' := continuousValueMultiplier_mul θ a ha
  map_zero' := continuousValueMultiplier_zero θ a ha
  map_add' := continuousValueMultiplier_add θ a ha
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one, continuousValueMultiplier_smul,
      continuousValueMultiplier_one]
  map_star' := continuousValueMultiplier_star θ a ha

end ContinuousValues
end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductDiffuse
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace Invariant233.ProductModel

def borelSetProjection (θ : ℕ → ℝ) (s : Set Base) (hs : MeasurableSet s) :
    Hilbert →L[ℂ] Hilbert :=
  multiplier θ (s.indicator (fun _ => (1 : ℂ))) 1 zero_le_one
    (measurable_const.indicator hs) (by
      intro x
      by_cases hx : x ∈ s <;> simp [hx])

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductFieldDiagonals
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
namespace Invariant233.ProductModel

abbrev S (m : ℤ) : Fiber →L[ℂ] Fiber :=
  (WeightedShift.shift m).toLinearIsometry.toContinuousLinearMap

def fieldCoefficient (F : Base → Fiber →L[ℂ] Fiber) (r : ℤ) (x : Base) : ℂ :=
  inner ℂ ((default : HilbertBasis ℤ ℂ Fiber) r)
    (F x ((default : HilbertBasis ℤ ℂ Fiber) 0))

theorem IsCovariantFieldRepresentation.measurable_fieldCoefficient
    {θ : ℕ → ℝ} {A : Hilbert →L[ℂ] Hilbert}
    {F : Base → Fiber →L[ℂ] Fiber} {B : ℝ}
    (h : IsCovariantFieldRepresentation θ A F B) (r : ℤ) :
    Measurable (fieldCoefficient F r) := by
  exact ((continuous_const.inner continuous_id).comp_stronglyMeasurable
    (h.2.2.1 ((default : HilbertBasis ℤ ℂ Fiber) 0))).measurable

theorem IsCovariantFieldRepresentation.norm_fieldCoefficient_le
    {θ : ℕ → ℝ} {A : Hilbert →L[ℂ] Hilbert}
    {F : Base → Fiber →L[ℂ] Fiber} {B : ℝ}
    (h : IsCovariantFieldRepresentation θ A F B) (r : ℤ) (x : Base) :
    ‖fieldCoefficient F r x‖ ≤ B := by
  let b := (default : HilbertBasis ℤ ℂ Fiber)
  calc
    ‖fieldCoefficient F r x‖ ≤ ‖b r‖ * ‖F x (b 0)‖ := norm_inner_le_norm _ _
    _ ≤ ‖b r‖ * (‖F x‖ * ‖b 0‖) :=
      mul_le_mul_of_nonneg_left ((F x).le_opNorm _) (norm_nonneg _)
    _ = ‖F x‖ := by rw [b.orthonormal.norm_eq_one, b.orthonormal.norm_eq_one]; ring
    _ ≤ B := h.2.1 x

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_DiagonalGauge
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Invariant233.DiagonalGauge

@[simp] theorem weight_apply (t : Circle) (k : ℤ) : weight t k = fourier k t := rfl

@[simp] theorem fiberOperator_apply (t : Circle) (v : Fiber) (k : ℤ) :
    fiberOperator t v k = fourier k t * v k := rfl

theorem norm_weight_le (t : Circle) : ‖weight t‖ ≤ 1 := by
  apply lp.norm_le_of_forall_le zero_le_one
  intro k
  exact (Circle.norm_coe _).le

theorem norm_fiberOperator_le (t : Circle) : ‖fiberOperator t‖ ≤ 1 := by
  unfold fiberOperator WeightedShift.diagonal
  exact (lp.norm_mapCLM_le 2 _ (norm_nonneg (weight t)) _).trans (norm_weight_le t)

theorem continuous_fiberOperator_apply (v : Fiber) :
    Continuous (fun t : Circle => fiberOperator t v) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact WeightedShift.diagonal_tendsto_apply
    (a := weight) (b := weight t) (l := 𝓝 t)
    (Eventually.of_forall norm_weight_le)
    (fun k => (fourier k).continuous.continuousAt) v

@[simp] theorem fiberOperator_zero : fiberOperator 0 = 1 := by
  ext v k
  simp [fiberOperator_apply]

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem fieldOperator_ae (t : Circle) (v : Lp Fiber 2 μ) :
    fieldOperator μ t v =ᵐ[μ] fun x => fiberOperator t (v x) :=
  (fiberOperator t).coeFn_compLpL v

theorem norm_fieldOperator_le (t : Circle) : ‖fieldOperator μ t‖ ≤ 1 :=
  (ContinuousLinearMap.norm_compLpL_le _).trans (norm_fiberOperator_le t)

@[simp] theorem fieldOperator_zero : fieldOperator μ 0 = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  filter_upwards [fieldOperator_ae μ 0 v] with x hx
  simpa only [fiberOperator_zero, one_apply_eq_self] using hx

variable [IsFiniteMeasure μ]

theorem continuous_fieldOperator_apply (v : Lp Fiber 2 μ) :
    Continuous (fun t : Circle => fieldOperator μ t v) := by
  apply continuous_iff_seqContinuous.mpr
  intro u t hut
  change Tendsto (fun n => fieldOperator μ (u n) v) atTop (𝓝 (fieldOperator μ t v))
  apply WeightedShift.lp_tendsto_of_ae_of_dominated (Lp.memLp v).norm
  · intro n
    filter_upwards [fieldOperator_ae μ (u n) v] with x hx
    rw [hx]
    simpa only [one_mul] using
      (fiberOperator (u n)).le_of_opNorm_le (norm_fiberOperator_le (u n)) (v x)
  · have hall : ∀ᵐ x ∂μ, ∀ n,
        fieldOperator μ (u n) v x = fiberOperator (u n) (v x) := by
      rw [ae_all_iff]
      intro n
      exact fieldOperator_ae μ (u n) v
    filter_upwards [hall, fieldOperator_ae μ t v] with x hx ht
    simp_rw [hx, ht]
    exact (continuous_fiberOperator_apply (v x)).tendsto t |>.comp hut

theorem continuous_conjugate_apply
    (A : Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ) (v : Lp Fiber 2 μ) :
    Continuous (fun t : Circle => conjugate μ A t v) := by
  apply InvariantProjection.continuous_apply_of_strong_continuous_of_bounded
    (continuous_fieldOperator_apply μ) (norm_fieldOperator_le μ)
  exact A.continuous.comp ((continuous_fieldOperator_apply μ v).comp continuous_neg)

omit [IsFiniteMeasure μ] in

theorem norm_conjugate_le
    (A : Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ) (t : Circle) :
    ‖conjugate μ A t‖ ≤ ‖A‖ := by
  unfold conjugate
  calc
    ‖fieldOperator μ t * A * fieldOperator μ (-t)‖ ≤
        (‖fieldOperator μ t‖ * ‖A‖) * ‖fieldOperator μ (-t)‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * ‖A‖) * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right (norm_fieldOperator_le μ t) (norm_nonneg _))
        (norm_fieldOperator_le μ (-t)) (norm_nonneg _) (by positivity)
    _ = ‖A‖ := by ring

omit [IsFiniteMeasure μ] in
@[simp] theorem conjugate_zero (A : Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ) :
    conjugate μ A 0 = A := by
  simp [conjugate]

end Invariant233.DiagonalGauge

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_GaugeFourierDiagonal
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Invariant233.DiagonalGauge

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

def coordinate (k : ℤ) : Lp Fiber 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k).compLpL 2 μ

def inclusion (j : ℤ) : Lp ℂ 2 μ →L[ℂ] Lp Fiber 2 μ :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 j).compLpL 2 μ

variable [IsFiniteMeasure μ]

theorem integrable_fourier_conjugate_apply
    (A : Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ) (r : ℤ) (v : Lp Fiber 2 μ) :
    Integrable (fun t : Circle => fourier (-r) t • conjugate μ A t v)
      AddCircle.haarAddCircle :=
  ((fourier (-r)).continuous.smul (continuous_conjugate_apply μ A v)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

omit [IsFiniteMeasure μ] in
theorem norm_fourier_conjugate_le
    (A : Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ) (r : ℤ) (t : Circle) :
    ‖fourier (-r) t • conjugate μ A t‖ ≤ ‖A‖ := by
  rw [norm_smul, show ‖fourier (-r) t‖ = 1 from Circle.norm_coe _, one_mul]
  exact norm_conjugate_le μ A t

def fourierOperator (A : Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ) (r : ℤ) :
    Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ :=
  StrongOperatorIntegral.operator
    (fun t : Circle => fourier (-r) t • conjugate μ A t)
    (integrable_fourier_conjugate_apply μ A r) ‖A‖
    (Filter.Eventually.of_forall (norm_fourier_conjugate_le μ A r))

@[simp] theorem fourierOperator_apply
    (A : Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ) (r : ℤ) (v : Lp Fiber 2 μ) :
    fourierOperator μ A r v =
      ∫ t : Circle, fourier (-r) t • conjugate μ A t v ∂AddCircle.haarAddCircle := rfl

end Invariant233.DiagonalGauge

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductGaugeFourier
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.ProductModel

variable {θ : ℕ → ℝ} {A : Hilbert →L[ℂ] Hilbert}
  {F : Base → Fiber →L[ℂ] Fiber} {B : ℝ}

def IsCovariantFieldRepresentation.matrixDiagonal
    (h : IsCovariantFieldRepresentation θ A F B) (r : ℤ) : Hilbert →L[ℂ] Hilbert :=
  (WeightedShift.shift r).toLinearIsometry.toContinuousLinearMap.compLpL 2 baseMeasure *
    multiplier θ (fieldCoefficient F r) B h.1
      (h.measurable_fieldCoefficient r) (h.norm_fieldCoefficient_le r)

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_ProductDeterminant
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.sequenceHilbertIntMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.ProductModel

def weightValue (θ c : ℕ → ℝ) (x : Base) : Set.Icc (0 : ℝ) 1 :=
  ⟨weight θ c x, weight_mem_Icc θ c x⟩

theorem measurable_weightValue (θ c : ℕ → ℝ) : Measurable (weightValue θ c) :=
  (measurable_weight θ c).subtype_mk

def weightMultiplier (θ c : ℕ → ℝ) : Hilbert →L[ℂ] Hilbert :=
  multiplier θ (fun x => (weight θ c x : ℂ)) 1 (by norm_num)
    (measurable_weight θ c).complex_ofReal (fun x => by
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (weight_mem_Icc θ c x).1] using (weight_mem_Icc θ c x).2)

@[simp] theorem weightedOperator_eq_shift_mul_weightMultiplier (θ c : ℕ → ℝ) :
    weightedOperator θ c = shiftOperator * weightMultiplier θ c := rfl

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductTracialInputs
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.ConcretePredual.evaluationLinearIsometryEquiv_apply _root_.OAI.Invariant233.ConcretePredual.evaluationLinearIsometry_apply _root_.OAI.Invariant233.ConcretePredual.evaluation_apply _root_.OAI.Invariant233.ConcretePredual.evaluation_vector _root_.OAI.Invariant233.ConcretePredual.inner_representingOperator _root_.OAI.Invariant233.ConcretePredual.norm_evaluation _root_.OAI.Invariant233.ConcretePredual.vectorFunctional_add_left _root_.OAI.Invariant233.ConcretePredual.vectorFunctional_add_right _root_.OAI.Invariant233.ConcretePredual.vectorFunctional_apply _root_.OAI.Invariant233.ConcretePredual.vectorFunctional_smul_left _root_.OAI.Invariant233.ConcretePredual.vectorFunctional_smul_right _root_.OAI.Invariant233.ConcretePredual.vector_coe _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProjectionMeetTrace.vectorFunctional_apply _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Invariant233.ProductModel

def weightedElement (θ c : ℕ → ℝ) : factor θ :=
  ⟨weightedOperator θ c, weightedOperator_mem_factor θ c⟩

def productTracialState (θ : ℕ → ℝ) : TracialState (factor θ) :=
  (traceVector_faithfulTracial θ).toTracialState

@[simp] theorem coe_weightedElement (θ c : ℕ → ℝ) :
    (weightedElement θ c : Hilbert →L[ℂ] Hilbert) = weightedOperator θ c := rfl

@[simp] theorem productTracialState_apply (θ : ℕ → ℝ) (a : factor θ) :
    productTracialState θ a = vectorTrace traceVector (a : Hilbert →L[ℂ] Hilbert) := rfl

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_PrefixDomination
attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.OneCoordinateCoupling

open CouplingMixture

instance triangleLaw_isFiniteMeasure : IsFiniteMeasure triangleLaw := by
  unfold triangleLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Invariant233.OneCoordinateCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductPrefixDomination
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.OrderedProductCoupling

open OneCoordinateCoupling CouplingMixture

instance sourcePairLaw_isProbabilityMeasure (P : Parameters) (i : ℕ) :
    IsProbabilityMeasure (pairLaw (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i)) :=
  pairLaw_isProbabilityMeasure (P.κ_nonneg i) (P.κ_le i) (P.m_ge i)
    (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i) (P.t_nonneg i) (P.t_le i)

instance leftTailLaw_isProbabilityMeasure (P : Parameters) (D : ℕ) :
    IsProbabilityMeasure (leftTailLaw P D) := by
  have : ∀ i : TailIndex D,
      IsProbabilityMeasure ((coordinateLaw P i).map (fun z => z.2.1)) :=
    fun _ => Measure.isProbabilityMeasure_map
      (show Measurable (fun z : CoordinateSample => z.2.1) by fun_prop).aemeasurable
  unfold leftTailLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance baseTailLaw_isProbabilityMeasure (D : ℕ) :
    IsProbabilityMeasure (baseTailLaw D) := by
  unfold baseTailLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Invariant233.OrderedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_PrefixReferenceIdentification
attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.OrderedProductCoupling

def referencePayload (D : ℕ) (xz : Endpoint × Endpoint) :
    PrefixPairs D × TailValues D :=
  ((fun i => (xz.1 i, xz.2 i)), fun i => xz.1 i)

end Invariant233.OrderedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductIdealSamplingLimit
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingCylinderWeak.quotient_cutCoordinates _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace Invariant233.ProductModel.IdealSampling

instance sourceMeasure_finite (I : Finset ℕ) : IsFiniteMeasure (sourceMeasure I) := by
  unfold sourceMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance law_finite (I D : Finset ℕ) (h α : ℝ) : IsFiniteMeasure (law I D h α) := by
  unfold law
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

@[fun_prop]
theorem endpointMap_measurable (I D : Finset ℕ) (h : ℝ) :
    Measurable (endpointMap I D h) := by
  apply measurable_fst.prodMk
  apply Measurable.of_eval
  intro i
  by_cases hi : i ∈ I
  · simpa [endpoint, endpointMap, hi, Function.comp_def] using
      (measurable_pi_apply i).comp measurable_snd
  · by_cases hd : i ∈ D
    · simp only [endpoint, hi, hd, ite_false, if_false, ite_true, if_true]
      have hx : Measurable (fun xz : EndpointPair => circleRepresentative (xz.1 i)) := by
        fun_prop
      have hz : Measurable (fun xz : EndpointPair => circleRepresentative (xz.2 i)) := by
        fun_prop
      have hδ : Measurable (fun xz : EndpointPair =>
          ScalarSampling.delta (circleRepresentative (xz.1 i))) :=
        hx.min (measurable_const.sub hx)
      have hc : Continuous (fun r : ℝ => (r : Circle)) := by fun_prop
      exact ((measurable_pi_apply i).comp measurable_fst).add
        (hc.measurable.comp ((measurable_const.mul hδ).mul hz))
    · simpa [endpoint, endpointMap, hi, hd, Function.comp_def] using
        (measurable_pi_apply i).comp measurable_fst

end Invariant233.ProductModel.IdealSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductIdealSamplingProduct
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Invariant233.ProductModel.IdealSampling

def coordinateEndpoint (I : Finset ℕ) (h : ℝ) (i : ℕ) (p : Circle × Circle) :
    Circle × Circle :=
  (p.1, if i ∈ I then p.2 else p.1 +
    ((h * ScalarSampling.delta (circleRepresentative p.1) *
      circleRepresentative p.2 : ℝ) : Circle))

def coordinateEvent (I : Finset ℕ) (α : ℝ) (i : ℕ) : Set (Circle × Circle) :=
  if i ∈ I then {p | circleRepresentative p.1 < circleRepresentative p.2}
  else {p | α ≤ ScalarSampling.delta (circleRepresentative p.1)}

@[fun_prop] theorem coordinateEndpoint_measurable (I : Finset ℕ) (h : ℝ) (i : ℕ) :
    Measurable (coordinateEndpoint I h i) := by
  apply measurable_fst.prodMk
  by_cases hi : i ∈ I
  · simpa [coordinateEndpoint, hi] using measurable_snd
  · simp only [hi, ite_false, if_false]
    have hx : Measurable (fun p : Circle × Circle => circleRepresentative p.1) := by
      fun_prop
    have hz : Measurable (fun p : Circle × Circle => circleRepresentative p.2) := by
      fun_prop
    have hd : Measurable (fun p : Circle × Circle => ScalarSampling.delta (circleRepresentative p.1)) :=
      hx.min (measurable_const.sub hx)
    have hc : Continuous (fun r : ℝ => (r : Circle)) := by fun_prop
    exact measurable_fst.add (hc.measurable.comp ((measurable_const.mul hd).mul hz))

end Invariant233.ProductModel.IdealSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingTestAlmostSure
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal BigOperators

namespace Invariant233.ProductModel.SamplingWeights

def sourceTestedError (p : ProductScaleData) (N : ℕ → Finset ℕ)
    (endpoint : Bool) (I : Finset ℕ) (E F : ℕ → Set ℝ)
    (n : ℕ) (θ : ℕ → ℝ) (x : Base) : ℝ :=
  ((N n).card : ℝ)⁻¹ * (∑ k ∈ N n,
    testedProduct endpoint (Finset.range (p.prefixCount (n + 1))) I
      ((p.m n : ℝ) ^ (-(3 / 5 : ℝ))) (1 / (p.m n : ℝ) ^ 2) E F θ k x) -
    testedIdeal endpoint (Finset.range (p.prefixCount (n + 1))) I
      ((p.m n : ℝ) ^ (-(3 / 5 : ℝ))) (1 / (p.m n : ℝ) ^ 2) E F x

end Invariant233.ProductModel.SamplingWeights

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_ProductFinitePolar
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter

namespace Invariant233.ProductModel

abbrev signedShift (m : ℤ) : Hilbert →L[ℂ] Hilbert :=
  (WeightedShift.shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 baseMeasure

end Invariant233.ProductModel

end

end OAI
end



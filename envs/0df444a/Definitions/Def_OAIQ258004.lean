-- Prove2me | Definitions.Def_OAIQ258004
-- name    : OAIQ258004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T05:14:51.558147+00:00
-- url     : https://prove2.me/theorems/74198409-dbe3-4177-bd3d-573ad95adbd8
-- title:
--   Definitions bundle OAIQ258004 of the split of OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 263 declarations of OpenAI's Lean: 164 definitions, 17 instances and 82 theorems. The definitions and types are `OAI.InvariantIsing.TensorGaussianKey`, `OAI.InvariantIsing.cavityFiberValues`, `OAI.InvariantIsing.coordinateProduct`, `OAI.InvariantIsing.countedFieldGroup`, `OAI.InvariantIsing.diagonalWardResidual`, `OAI.InvariantIsing.fieldAffineValue`, `OAI.InvariantIsing.fieldBallSimple`, `OAI.InvariantIsing.fieldEndpointCoordinateTest`, `OAI.InvariantIsing.fieldEnergyCoordinates`, `OAI.InvariantIsing.fieldEnergyMarkLaw`, `OAI.InvariantIsing.fieldFinalPrefix`, `OAI.InvariantIsing.fieldFiniteFamily`, `OAI.InvariantIsing.fieldFiniteLogCosh`, `OAI.InvariantIsing.fieldFiniteValue`, `OAI.InvariantIsing.fieldFixedAffine`, `OAI.InvariantIsing.fieldHeightFiniteList`, `OAI.InvariantIsing.fieldHeightFiniteStep`, `OAI.InvariantIsing.fieldHeightJointValue`, `OAI.InvariantIsing.fieldInteriorPrefix`, `OAI.InvariantIsing.fieldInteriorTail`, `OAI.InvariantIsing.fieldLogCoshFamily`, `OAI.InvariantIsing.fieldNNIncrement`, `OAI.InvariantIsing.fieldProjectionDistance`, `OAI.InvariantIsing.fieldRegularizedHeight`, `OAI.InvariantIsing.fieldRegularizedIncrements`, `OAI.InvariantIsing.fieldRegularizedRoot`, `OAI.InvariantIsing.fieldSitePermutation`, `OAI.InvariantIsing.fieldVaryingMean`, `OAI.InvariantIsing.fieldVaryingSquares`, `OAI.InvariantIsing.fieldVaryingValue`, `OAI.InvariantIsing.finiteEnergyDerivative`, `OAI.InvariantIsing.finiteGibbsVariation`, `OAI.InvariantIsing.finiteSpectralSlope`, `OAI.InvariantIsing.finiteThermalScalar`, `OAI.InvariantIsing.gaussianGramResolvent`, `OAI.InvariantIsing.gaussianGramStieltjes`, `OAI.InvariantIsing.gaussianWardCorrection`, `OAI.InvariantIsing.gibbsKernelCorrection`, `OAI.InvariantIsing.gordonCurveMean`, `OAI.InvariantIsing.gordonCurveSlope` and 124 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `InvariantIsing_Arrays_CoordinateWard`, `InvariantIsing_Arrays_NSpinCascade`, `InvariantIsing_Arrays_NSpinTensorCascade`, `InvariantIsing_Arrays_NSpinTensorFrozen`, `InvariantIsing_Arrays_NSpinTensorGaussianLaw`, `InvariantIsing_Arrays_NSpinTensorHaarFluctuation`, `InvariantIsing_Arrays_NSpinTensorPairConditioning`, `InvariantIsing_Arrays_OffDiagonalWard`, `InvariantIsing_Arrays_OverlapPathCompact`, `InvariantIsing_Arrays_QuantileProductPath`, `InvariantIsing_Arrays_ReplicaWardPaths`, `InvariantIsing_Arrays_TensorArrayDiagonalWard`, `InvariantIsing_Arrays_TensorArrayWard`, `InvariantIsing_Arrays_TensorCoefficientDerivative`, `InvariantIsing_Arrays_TensorContactRegion`, `InvariantIsing_Arrays_TensorDiagonalPrincipalObservables`, `InvariantIsing_Arrays_TensorFieldDerivative`, `InvariantIsing_Arrays_TensorFieldDerivativeIntegrability`, `InvariantIsing_Arrays_TensorFieldTailBridge`, `InvariantIsing_Arrays_TensorFiniteWard`, `InvariantIsing_Arrays_TensorGGRate`, `InvariantIsing_Arrays_TensorHaarWard`, `InvariantIsing_Arrays_TensorLeafTail`, `InvariantIsing_Arrays_TensorPrincipalObservables`, `InvariantIsing_Arrays_TensorTruncatedDiagonalWard`, `InvariantIsing_Arrays_TensorTruncatedWard`, `InvariantIsing_Arrays_TensorWardCorrectionBound`, `InvariantIsing_Arrays_TensorWardError`, `InvariantIsing_Arrays_TensorZeroAmplitude`, `InvariantIsing_Cavity_CavityFiberFactor`, `InvariantIsing_Cavity_CavityFiniteDeficit`, `InvariantIsing_Cavity_CavityGaussianRows`, `InvariantIsing_Cavity_CavityGroupGaussian`, `InvariantIsing_Cavity_OffsetFieldPressure`, `InvariantIsing_Core_FiniteFieldLabels`, `InvariantIsing_Core_MixedSpectralFeatures`, `InvariantIsing_Core_Model`, `InvariantIsing_Core_TailOrder`, `InvariantIsing_Fields_CanonicalOrthogonalLaw`, `InvariantIsing_Fields_FieldAffineRecursion`, `InvariantIsing_Fields_FieldCoordinateDerivative`, `InvariantIsing_Fields_FieldEnergyCoordinates`, `InvariantIsing_Fields_FieldFiniteFamily`, `InvariantIsing_Fields_FieldFiniteRecursion`, `InvariantIsing_Fields_FieldHeightBoundaryContinuity`, `InvariantIsing_Fields_FieldHeightFinalOrder`, `InvariantIsing_Fields_FieldHeightInteriorLaw`, `InvariantIsing_Fields_FieldHeightInteriorOrder`, `InvariantIsing_Fields_FieldHeightJoint`, `InvariantIsing_Fields_FieldHeightRegularization`, `InvariantIsing_Fields_FieldHeightUpdate`, `InvariantIsing_Fields_FieldProjectionLoss`, `InvariantIsing_Fields_FieldPublishedEvaluation`, `InvariantIsing_Fields_FieldQuantizer`, `InvariantIsing_Fields_FieldRefineIncrements`, `InvariantIsing_Fields_FieldSpinTransition`, `InvariantIsing_Fields_FieldVaryingRecursion`, `InvariantIsing_Fields_FieldVectorSampling`, `InvariantIsing_Fields_PhysicalFieldPermutation`, `InvariantIsing_Fields_PriorFieldLogNormalizer`, `InvariantIsing_Fields_PriorFrozenReference`, `InvariantIsing_Fields_PriorSpinLeafConditioning`, `InvariantIsing_Fields_SeedForestPairData`, `InvariantIsing_Fields_SeedPairStep`, `InvariantIsing_Fields_SimpleFieldData`, `InvariantIsing_Fields_SpinGroupProjection`, `InvariantIsing_Fields_SpinHammingBall`, `InvariantIsing_Fields_SpinPairSubGaussian`, `InvariantIsing_Fields_VectorGaussianTransition`, `InvariantIsing_Fields_VectorPairIntegral`, `InvariantIsing_Fields_VectorTerminalCascade`, `InvariantIsing_Fields_VectorTerminalLabeled`, `InvariantIsing_Fields_ZeroFieldPopulations`, `InvariantIsing_Gaussian_GaussianGramEmpiricalTransform`, `InvariantIsing_Gaussian_GaussianGramResolvent`, `InvariantIsing_Gaussian_GordonCurveMean`, `InvariantIsing_Haar_HaarCompactness`, `InvariantIsing_Haar_HaarExponentialPolynomial`, `InvariantIsing_Haar_HaarFunctionalCurvature`, `InvariantIsing_Haar_HaarGroupTopology`, `InvariantIsing_Haar_HaarHeatContinuity`, `InvariantIsing_Haar_HaarHeatLinear`, `InvariantIsing_Haar_HaarHeatLogBarrier`, `InvariantIsing_Haar_HaarKernelConvolution`, `InvariantIsing_Haar_HaarLogBarrier`, `InvariantIsing_Haar_HaarLogCurvature`, `InvariantIsing_Haar_HaarPolynomialCurvature`, `InvariantIsing_Haar_HaarPolynomialGamma`, `InvariantIsing_Haar_HaarPolynomialHeat`, `InvariantIsing_Haar_HaarPolynomialInvariantSpace`, `InvariantIsing_Haar_HaarPolynomialKernel`, `InvariantIsing_Haar_HaarPolynomialLaplacian`, `InvariantIsing_Haar_HaarPolynomialSpace`, `InvariantIsing_Haar_ReflectionPairCurve`, `InvariantIsing_Haar_ReflectionSegment`, `InvariantIsing_Haar_ReflectionSegmentDerivative`, `InvariantIsing_Haar_RotationMatrix`, `InvariantIsing_Haar_SpecialSkewRotation`, `InvariantIsing_Magnetic_MagneticContinuationGenerator`, `InvariantIsing_Magnetic_MagneticContinuationTime`, `InvariantIsing_Magnetic_MagneticGaussianCovariance`, `InvariantIsing_Magnetic_MagneticStationaryFamily`, `InvariantIsing_Magnetic_MagneticWeightedJet`, `InvariantIsing_Magnetic_RestrictedPressure`, `InvariantIsing_Pressure_Concentration`, `InvariantIsing_Pressure_PressureMean`, `InvariantIsing_Spectral_ResolventMeasureUniqueness`, `InvariantIsing_Spectral_SpectralArrayEnergy`, `InvariantIsing_Spectral_SpectralArrayGG`, `InvariantIsing_Spectral_SpectralArrayGeometry`, `InvariantIsing_Spectral_SpectralBallQuantizer`, `InvariantIsing_Spectral_SpectralCalculus`, `InvariantIsing_Spectral_SpectralDiagonalWardLimits`, `InvariantIsing_Spectral_SpectralEnergy`, `InvariantIsing_Spectral_SpectralGGGeometry`, `InvariantIsing_Spectral_SpectralOverlapPaths`, `InvariantIsing_Spectral_SpectralPartition`, `InvariantIsing_Spectral_SpectralPartitionPaths`, `InvariantIsing_Spectral_SpectralPaths`, `InvariantIsing_Spectral_SpectralPermutation`, `InvariantIsing_Spectral_SpectralProjectionMass`, `InvariantIsing_Spectral_SpectralQuantilePaths`, `InvariantIsing_Spectral_SpectralWardAlgebra`, `InvariantIsing_Spectral_SpectralWardLimits`, `IsingPerceptron_JointGGClosure`, `IsingPerceptron_MonomialGgAtMinimum`.
--
--   **Imports.** It imports the published bundles `Def_InvariantIsing` and `Def_IsingFiniteness`; the bundles `OAIQ258000`, `OAIQ258001` and `OAIQ258002` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ258005`; the statements `OAI.InvariantIsing.cavity_finite_log_evaluation`, `OAI.InvariantIsing.finiteSpectrum_restrictedPressure_entropy_upper`, `OAI.InvariantIsing.gaussianPatternStieltjes_tendsto`, `OAI.InvariantIsing.magnetic_affine_field_subsequence_lower`, `OAI.InvariantIsing.restricted_cavity_finite_log_evaluation`, `OAI.InvariantIsing.spinPriorFlat_leafPrefix_mean`, `OAI.InvariantIsing.tensorFlat_leafPrefix_mean` and `OAI.InvariantIsing.vectorTerminal_pair_formula`; the proofs of `OAI.InvariantIsing.cavity_finite_labeled_moment`, `OAI.InvariantIsing.cavity_finite_model_numerator`, `OAI.InvariantIsing.cavity_finite_original_integrability`, `OAI.InvariantIsing.cavity_finite_trial_preliminary_lower`, `OAI.InvariantIsing.cavity_labeled_projector_joint_law`, `OAI.InvariantIsing.cavity_linear_rooted_depth_evaluation`, `OAI.InvariantIsing.cavity_spectral_haar_test_tendsto`, `OAI.InvariantIsing.cavity_strict_finite_overlap_test`, `OAI.InvariantIsing.cavity_tree_pressure_capped_increment`, `OAI.InvariantIsing.closedMagneticScalarCurvature_hasDerivAt_time`, `OAI.InvariantIsing.compact_spectral_field_pressure_tendsto_of_mem`, `OAI.InvariantIsing.compact_spectral_pressure_tendsto_of_mem`, `OAI.InvariantIsing.entropyFunctional_zero`, `OAI.InvariantIsing.finite_type_field_pressure_tendsto`, `OAI.InvariantIsing.gaussianPatternStieltjes_tendsto`, `OAI.InvariantIsing.gaussianPatternTranspose_lower_edge`, `OAI.InvariantIsing.general_spectral_mean_field_positive_part_tendsto`, `OAI.InvariantIsing.ground_state_limit`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits`, `OAI.InvariantIsing.magneticClosedCurvature_compare_initial`, `OAI.InvariantIsing.magneticEntropyFunctional_lower`, `OAI.InvariantIsing.marchenkoPastur_proved`, `OAI.InvariantIsing.physical_mean_pressure_tendsto`, `OAI.InvariantIsing.physical_mean_wasserstein_field_pressure_tendsto`, `OAI.InvariantIsing.positive_temperature_pressure`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae`, `OAI.InvariantIsing.random_pressure_tendsto_ae`, `OAI.InvariantIsing.restricted_cavity_finite_log_evaluation`, `OAI.InvariantIsing.restricted_cavity_finite_trial_preliminary_lower`, `OAI.InvariantIsing.selected_spectral_pressure_tendsto`, `OAI.InvariantIsing.spectral_clip_mean_field_pressure_close`, `OAI.InvariantIsing.spectral_clip_mean_pressure_close`, `OAI.InvariantIsing.vectorTerminal_pair_formula`, `OAI.IsingPerceptron.cascadeEnergyLog_total_mean` and `OAI.IsingPerceptron.enriched_poisson_unshifted`.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Sort
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Order.Lattice
import Mathlib.Order.Disjointed
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Fin.InsertNth
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Representation
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.StrongLaw
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_InvariantIsing
import Definitions.Def_IsingFiniteness
import Definitions.Def_OAIQ258000
import Definitions.Def_OAIQ258001
import Definitions.Def_OAIQ258002

section
-- module Solutions.OAIQ258_II.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
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
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-volume invariant Ising pressure

The spin prior is uniform probability, as in (1.1) and (7.1) of
*All-temperature pressure for orthogonally invariant Ising spin glasses*.
These deterministic comparison lemmas do not assume any asymptotic pressure formula.
-/

noncomputable section

open scoped BigOperators

namespace InvariantIsing

/-- Quadratic interaction energy, including the diagonal. -/
def quadraticEnergy {N : ℕ} (J : Matrix (Fin N) (Fin N) ℝ) (σ : Spin N) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, spinValue (σ i) * J i j * spinValue (σ j)

/-- Finite-volume pressure, normalized per site and by the probability spin prior. -/
def pressure {N : ℕ} (J : Matrix (Fin N) (Fin N) ℝ) (c : Fin N → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * logPartition (fun σ => quadraticEnergy J σ + fieldEnergy c σ)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_CoordinateWard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The coordinate Haar Ward identity for the Ising Hamiltonian

This proves the finite-dimensional identity for the unperturbed model with an
arbitrary deterministic spin prior and magnetic field.
-/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

/-- Spectral coordinate of a rotated Ising spin. -/
def spinCoordinate {N : ℕ} (U : Orthogonal N) (σ : Spin N) (i : Fin N) : ℝ :=
  matrixRotation U (spinVector σ) i

def coordinateProduct {N : ℕ} (i j : Fin N) (U : Orthogonal N) (σ : Spin N) : ℝ :=
  spinCoordinate U σ i * spinCoordinate U σ j

def orbitHamiltonian {N : ℕ} (eig c : Fin N → ℝ) (U : Orthogonal N) (σ : Spin N) : ℝ :=
  rotatedEnergy eig (matrixRotation U) σ + fieldEnergy c σ

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_MonomialGgAtMinimum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Monomial Gg At Minimum. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]

lemma measurable_backwardValue (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {u : ℕ → S × A → S} {F : S → ℝ}
    (hu : ∀ i, Measurable (u i)) (hF : Measurable F) (i : ℕ) :
    Measurable (backwardValue n b μ u F i) :=
  measurable_cascadeRecursion _ _ _ (fun j => hu (i+j)) hF

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_JointGGClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint G G Closure. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def contactGGRate (N j : ℕ) (L B : ℝ) : ℝ :=
  let a := perturbationAmplitude N j
  let c := N*perturbationWeight j/a^2
  let θ := 1/perturbationScale N
  let δ := 2*N*Real.sqrt (L/N)
  2*B*((2*c+θ^2)/(2*θ)+c*(a*contactStep N)+4*δ/(a*contactStep N))/a

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinCascade
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Gaussian cascade marking for the actual finite Ising partition function at
a fixed orthogonal rotation. The Haar variable is fixed in this result.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

def rotatedFieldTerminal {N : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c z : Fin N → ℝ) : ℝ :=
  logPartition (fun σ => rotatedEnergy eig U σ + fieldEnergy (c + z) σ)

def rotatedCascadeValue {N : ℕ} (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (eig : Fin N → ℝ) (U : Rotation N) (c z : Fin N → ℝ) : ℝ :=
  IsingPerceptron.cascadeRecursion n b (fun i => vectorGaussianLaw N (v i))
    (fun _ p => p.1 + p.2) (rotatedFieldTerminal eig U c) z

def rotatedEnrichedPressure {N : ℕ} (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (root : ℝ≥0) (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∫ z, rotatedCascadeValue n b v eig U c z
    ∂(vectorGaussianLaw N root : Measure (Fin N → ℝ))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_Concentration
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Haar concentration for Ising pressure

Frobenius Lipschitz continuity and measurability give concentration of the
Ising pressure about a median.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace InvariantIsing

lemma measurable_specialRotation_eval {N : ℕ} (v : EuclideanSpace ℝ (Fin N))
    (i : Fin N) : Measurable (fun U : SpecialOrthogonal N => specialRotation U v i) := by
  simp only [specialRotation_apply]
  apply Finset.measurable_sum
  intro j _
  have he : Measurable (fun U : SpecialOrthogonal N =>
      (U : Matrix (Fin N) (Fin N) ℝ) i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_subtype_coe)
  exact he.mul_const (v j)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorCascade
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The finite spectral-monomial enriched Ising model. Gaussian marks have a
separate variance at every site/tensor coordinate and every cascade level.
The spectral coefficients retain their actual dependence on the rotation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

def tensorGaussianLaw {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (v : SpinTensorIndex I degree → ℝ≥0) :
    ProbabilityMeasure (SpinTensorIndex I degree → ℝ) :=
  ⟨Measure.pi (fun i => gaussianReal 0 (v i)), (by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

def tensorCascadeLaw {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (b : ℕ → ℝ)
    (v : ℕ → SpinTensorIndex I degree → ℝ≥0) :
    Measure (IsingPerceptron.NoiseTree (SpinTensorIndex I degree → ℝ) n) :=
  IsingPerceptron.noiseCascadeLaw (SpinTensorIndex I degree → ℝ) n b
    (fun i => tensorGaussianLaw I degree (v i))

/-- The actual sum of the root and all Gaussian marks on a sampled leaf. -/
def tensorLeafState {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) : (n : ℕ) → (SpinTensorIndex I degree → ℝ) →
    IsingPerceptron.NoiseLeaf (SpinTensorIndex I degree → ℝ) n → (SpinTensorIndex I degree → ℝ)
  | 0, z, _ => z
  | n + 1, z, leaf => tensorLeafState I degree n (z + leaf.2.1) leaf.2.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_MixedSpectralFeatures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mixed-rotation tensor covariances for Gaussian mean comparison. -/

noncomputable section

open scoped BigOperators

namespace InvariantIsing

def mixedProjectedOverlap {N : ℕ} (U V : Rotation N) (I : Finset (Fin N))
    (σ τ : Spin N) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i ∈ I, U (spinVector σ) i * V (spinVector τ) i

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorGaussianLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The flat countable Gaussian field has the actual root/forest mark law. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

def tensorNodeTag {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (w : Option (ForestVertex n))
    (i : SpinTensorIndex I degree) : ℕ :=
  Encodable.encode ((nodeAddress n w).length, nodeAddress n w, i)

def tensorStandardGaussianNodes {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (g : ℕ → ℝ)
    (w : Option (ForestVertex n)) (i : SpinTensorIndex I degree) : ℝ :=
  g (tensorNodeTag I degree n w i)

def tensorGaussianNodes {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (g : ℕ → ℝ) (w : Option (ForestVertex n)) (i : SpinTensorIndex I degree) : ℝ :=
  (NNReal.sqrt (v (nodeAddress n w).length i) : ℝ) * tensorStandardGaussianNodes I degree n g w i

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorFrozen
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A selected actual spectral/tree monomial as an independent Gaussian factor. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

abbrev TensorGaussianKey {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) := ℕ × List ChildLabel × SpinTensorIndex I degree

/-- Namespace zero contains the linear field; namespace `j+1` contains
precisely the `j`th spectral tensor at all ancestor levels. -/
def tensorNamespaceTag {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (q : TensorGaussianKey I degree) : ℕ :=
  match q.2.2 with
  | Sum.inl a => Nat.pair 0 (Encodable.encode (q.1, q.2.1, a))
  | Sum.inr a => Nat.pair (a.1 + 1) (Encodable.encode (q.1, q.2.1, a.2))

def tensorLinearCoefficients {N : ℕ} (n : ℕ) (h : ℕ → ℝ)
    (x : Spin N × LabeledLeaf n) : ℕ →₀ ℝ :=
  treeFieldCoefficients n x.2 (fun i => pathAmplitude h i) (fun i => spinValue (x.1 i))

def tensorFrozenLaw {N : ℕ} (μ : Measure (SpecialOrthogonal N)) (n : ℕ) (b : ℕ → ℝ) (j : ℕ) :
    Measure (TensorFrozenData N n j) :=
  (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod (otherNamespacesLaw (j + 1))

instance tensorFrozenLaw_probability {N : ℕ} (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (n : ℕ) (b : ℕ → ℝ) (j : ℕ) : IsProbabilityMeasure (tensorFrozenLaw μ n b j) := by
  unfold tensorFrozenLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorHaarFluctuation
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full Haar, Gaussian-root, and cascade fluctuations for the actual finite tensor model. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

/-- Independent common Gaussian root and marked cascade. -/
def tensorRootTreeLaw {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (b : ℕ → ℝ)
    (v : ℕ → SpinTensorIndex I degree → ℝ≥0) (root : SpinTensorIndex I degree → ℝ≥0) :
    Measure ((SpinTensorIndex I degree → ℝ) × NoiseTree (SpinTensorIndex I degree → ℝ) n) :=
  (tensorGaussianLaw I degree root : Measure (SpinTensorIndex I degree → ℝ)).prod
    (tensorCascadeLaw I degree n b v)

instance tensorRootTreeLaw_probability {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (b : ℕ → ℝ)
    (v : ℕ → SpinTensorIndex I degree → ℝ≥0) (root : SpinTensorIndex I degree → ℝ≥0) :
    IsProbabilityMeasure (tensorRootTreeLaw I degree n b v root) := by
  let : IsProbabilityMeasure (tensorCascadeLaw I degree n b v) :=
    (noiseCascadeLaw (SpinTensorIndex I degree → ℝ) n b
      (fun i => tensorGaussianLaw I degree (v i))).prop
  unfold tensorRootTreeLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorPairConditioning
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conditional independent spin residuals at two sampled cascade leaves. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators ENNReal NNReal

namespace InvariantIsing

def spinLeafPairJoin {N n : ℕ}
    (p : (Fin 2 → LabeledLeaf n) × (Fin 2 → Spin N)) : Fin 2 → Spin N × LabeledLeaf n :=
  fun i => (p.2 i, p.1 i)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_OffDiagonalWard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact two-replica off-diagonal Haar Ward identity. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def offCoordinateProduct {N : ℕ} (i j : Fin N) (F : Spin N → Spin N → ℝ)
    (U : Orthogonal N) (x : Spin N × Spin N) : ℝ :=
  spinCoordinate U x.1 i * spinCoordinate U x.2 j * F x.1 x.2

def offCoordinateVariation {N : ℕ} (i j : Fin N) (F : Spin N → Spin N → ℝ)
    (U : Orthogonal N) (x : Spin N × Spin N) : ℝ :=
  (spinCoordinate U x.1 j * spinCoordinate U x.2 j -
    spinCoordinate U x.1 i * spinCoordinate U x.2 i) * F x.1 x.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_OverlapPathCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sequential L1 compactness of bounded monotone overlap paths. The
proof extracts the values on the rationals and discards only the
countable discontinuity set of the resulting monotone path. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace InvariantIsing

def rationalLowerPath (f : ℚ → Icc (0 : ℝ) 1) : OverlapPath where
  val x := sSup (rationalLowerValues f x)
  monotone := by
    intro x y hxy
    apply csSup_le_csSup (rationalLowerValues_bdd f y) (rationalLowerValues_nonempty f x)
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨q, hq.trans_le hxy, rfl⟩
  nonneg x := by
    obtain ⟨q, hq⟩ := exists_rat_lt x
    exact (f q).property.1.trans (le_csSup (rationalLowerValues_bdd f x) ⟨q, hq, rfl⟩)
  le_one x := by
    apply csSup_le (rationalLowerValues_nonempty f x)
    rintro _ ⟨q, _, rfl⟩
    exact (f q).property.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralArrayGG
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multivariate monomial GG closure for the finite vector of spectral overlaps. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace InvariantIsing

def spectralEntryMonomial {m : ℕ} (d : Fin m → ℕ) (x : SpectralEntry m) : ℝ :=
  ∏ a, (x a : ℝ) ^ d a

def spectralBlockLink (m n i j : ℕ) (x : SpectralArray m) : SpectralBlock m n × SpectralEntry m :=
  (spectralBlockView m n x, x (i, j))

def spectralBlockPairCoordinate (m n : ℕ)
    (i : ((Fin n × Fin n) × Fin m) ⊕ Fin m)
    (x : SpectralBlock m n × SpectralEntry m) : ℝ :=
  match i with
  | Sum.inl i => x.1 i.1.1 i.1.2 i.2
  | Sum.inr i => x.2 i

def spectralMonomialResidual {m : ℕ} (μ : Measure (SpectralArray m)) (n : ℕ) (i : Fin n)
    (D : SpectralBlock m n → ℝ) (d : Fin m → ℕ) : ℝ :=
  (n : ℝ) * (∫ x, D (spectralBlockView m n x) * spectralEntryMonomial d (x (i, n)) ∂μ) -
    (∫ x, D (spectralBlockView m n x) ∂μ) * (∫ x, spectralEntryMonomial d (x (0, 1)) ∂μ) -
    ∑ j ∈ Finset.univ.erase i,
      ∫ x, D (spectralBlockView m n x) * spectralEntryMonomial d (x (i, j)) ∂μ

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralArrayGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gram structure and replica symmetry for spectral arrays retaining common disorder. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology Matrix

namespace InvariantIsing

def permuteSpectralArray {m : ℕ} (e : ℕ → ℕ) (x : SpectralArray m) : SpectralArray m :=
  fun ij => x (e ij.1, e ij.2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralGGGeometry
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Published ultrametricity and synchronization applied to spectral GG limits. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Topology Matrix

namespace InvariantIsing

def spectralLinearEntry {m : ℕ} (w : Fin m → ℝ) (x : SpectralEntry m) : ℝ :=
  ∑ a, w a * (x a : ℝ)

def spectralLinearArray {m : ℕ} (w : Fin m → ℝ) (x : SpectralArray m) : RealArray :=
  fun i j => spectralLinearEntry w (x (i,j))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Differentiation of the finite spectral inverse. The inverse function
theorem is applied to the already constructed inverse; no regularity of
that inverse is assumed.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

/-- First derivative of `x R(x)`, in a form without cancellation at zero. -/
def finiteEnergyDerivative (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (x : ℝ) : ℝ :=
  finiteInverse ρ eig hρ hρsum x +
    x * (-1 / finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite spectral-group functions from manuscript `rot:f`. -/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

def projectedResolvent (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) (x : ℝ) : ℝ :=
  if 0 < x then ρ a / (finiteInverse ρ eig hρ hρsum x - eig a) else 0

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralOverlapPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reconstructed finite-alphabet overlap paths in manuscript `rot:full-paths`.
The formulas and their positivity and sum constraints are proved here;
identification with limiting Gibbs overlaps is separate. -/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

def spectralGroupPath (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) (s : ℝ) : ℝ :=
  ∫ r in 0..p s, spectralPathDensity ρ eig hρ hρsum p a r

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_QuantileProductPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript replica-product path as a proved quantile kernel. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

def replicaProductDiagonal (da db : ℝ) (a b : ℝ → ℝ) : ℝ :=
  da * db - ∫ s, a s * b s ∂pathMeasure

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_ReplicaWardPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extract pointwise path equations from continuous Ward tests, then pass
those equations to symbols and right roots. All Ward hypotheses in this
module are internal consequences to be supplied by rotation calculus. -/

noncomputable section

open MeasureTheory IsingPerceptron Set Filter
open scoped Topology

namespace InvariantIsing

def diagonalWardResidual (ρa ρb δ da db : ℝ) (a b : ℝ → ℝ) : ℝ :=
  ρa * db - ρb * da + δ * replicaProductDiagonal da db a b

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorWardError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite covariance derivative contractions in the tensor perturbation
error of the spectral Ward identity (manuscript, §3, lines 421--439). -/

noncomputable section

open IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def projectedOverlapEndpointDerivative {N : ℕ} (U : Orthogonal N) (K : Finset (Fin N))
    (i j : Fin N) (σ τ : Spin N) : ℝ :=
  (N : ℝ)⁻¹ * ((if i ∈ K then spinCoordinate U σ j * spinCoordinate U τ i else 0) -
    (if j ∈ K then spinCoordinate U σ i * spinCoordinate U τ j else 0))

def projectedEndpointContraction {N : ℕ} (U : Orthogonal N)
    (I J K : Finset (Fin N)) (η θ σ τ : Spin N) : ℝ :=
  (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ I, ∑ j ∈ J,
    spinCoordinate U η i * spinCoordinate U θ j * projectedOverlapEndpointDerivative U K i j σ τ

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorFiniteWard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-prior Gaussian insertions in the spectral Haar Ward calculation.
The covariance correction is derived by Gaussian integration by parts, with
no assumed Ward identity. Finite spin/leaf restrictions are permitted to
have zero prior weights. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {S : Type*} [Fintype S]

/-- The exact correction obtained from inserting the derivative of a
Gaussian Hamiltonian into a normalized finite Gibbs average. The kernel
need not be symmetric: its first endpoint is the differentiated one. -/
def gaussianWardCorrection (w H O : S → ℝ) (K : S → S → ℝ) : ℝ :=
  gibbsAverage w H (fun x => O x * K x x) -
    gibbsPairAverage w H (fun x y => O x * K x y) -
    gibbsPairAverage w H (fun x y => O x * (K y x + K y y)) +
    2 * gibbsTripleAverage w H (fun x y z => O x * K y z)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorCoefficientDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate-plane derivatives of the actual finite spectral tensor
coefficients, with uniform finite-dimensional bounds for Haar differentiation. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

/-- A normalized spectral coordinate has a uniformly bounded plane derivative. -/
def spectralSpinPlaneDerivative {N : ℕ} (U : Orthogonal N) (σ : Spin N)
    (i j a : Fin N) : ℝ :=
  (if a = i then spinCoordinate U σ j / Real.sqrt (N : ℝ) else 0) -
    (if a = j then spinCoordinate U σ i / Real.sqrt (N : ℝ) else 0)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorHaarWard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Gaussian/Haar Ward identities. The Gaussian correction is
proved from integration by parts, while Haar invariance is differentiated
on genuine determinant-one plane rotations. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology

namespace InvariantIsing

variable {S : Type*} [Fintype S]

def finiteGibbsVariation (w H O dH dO : S → ℝ) : ℝ :=
  gibbsAverage w H dO + gibbsAverage w H (fun x => O x * dH x) -
    gibbsAverage w H O * gibbsAverage w H dH

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorTruncatedWard
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite spin/leaf pair application of the spectral Haar Ward identity.
The spin test is fixed under rotations and may be any function of total
overlap. Arbitrary finite leaf restrictions and zero prior weights are allowed. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

variable {S : Type*}

def tensorRestrictionBase {N : ℕ} (eig c : Fin N → ℝ) {n : ℕ}
    (x : S → Spin N × LabeledLeaf n) (U : SpecialOrthogonal N) (s : S) : ℝ :=
  orbitHamiltonian eig c (specialToOrthogonal U) (x s).1

def tensorRestrictionOffObservable {N n : ℕ} (i j : Fin N)
    (F : Spin N → Spin N → ℝ) (x : S → Spin N × LabeledLeaf n)
    (U : SpecialOrthogonal N) (p : S × S) : ℝ :=
  offCoordinateProduct i j F (specialToOrthogonal U) ((x p.1).1, (x p.2).1)

def tensorRestrictionOffVariation {N n : ℕ} (i j : Fin N)
    (F : Spin N → Spin N → ℝ) (x : S → Spin N × LabeledLeaf n)
    (U : SpecialOrthogonal N) (p : S × S) : ℝ :=
  offCoordinateVariation i j F (specialToOrthogonal U) ((x p.1).1, (x p.2).1)

def tensorRestrictionMainVariation {N n : ℕ} (eig : Fin N → ℝ) (i j : Fin N)
    (x : S → Spin N × LabeledLeaf n) (U : SpecialOrthogonal N) (p : S × S) : ℝ :=
  (eig i - eig j) * (coordinateProduct i j (specialToOrthogonal U) (x p.1).1 +
    coordinateProduct i j (specialToOrthogonal U) (x p.2).1)

def tensorRestrictionPairBase {N n : ℕ} (eig c : Fin N → ℝ)
    (x : S → Spin N × LabeledLeaf n) (U : SpecialOrthogonal N) (p : S × S) : ℝ :=
  tensorRestrictionBase eig c x U p.1 + tensorRestrictionBase eig c x U p.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorTruncatedDiagonalWard
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The one-replica diagonal Haar Ward identity for the actual finite
spin/leaf tensor model. The main quadratic coefficient has no extra factor two. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

variable {S : Type*}

def tensorRestrictionDiagonalObservable {N n : ℕ} (i j : Fin N)
    (x : S → Spin N × LabeledLeaf n) (U : SpecialOrthogonal N) (s : S) : ℝ :=
  coordinateProduct i j (specialToOrthogonal U) (x s).1

def tensorRestrictionDiagonalVariation {N n : ℕ} (i j : Fin N)
    (x : S → Spin N × LabeledLeaf n) (U : SpecialOrthogonal N) (s : S) : ℝ :=
  spinCoordinate (specialToOrthogonal U) (x s).1 j ^ 2 -
    spinCoordinate (specialToOrthogonal U) (x s).1 i ^ 2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorWardCorrectionBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform bounds on the complete finite Gaussian Ward correction after
spectral coordinate contraction. Constants do not depend on the leaf cutoff. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {S ι : Type*} [Fintype S]

/-- The Gaussian correction written in terms of a contracted observable
and kernel. Its three arguments retain the observable and both endpoints. -/
def gibbsKernelCorrection (w H : S → ℝ) (C : S → S → S → ℝ) : ℝ :=
  gibbsAverage w H (fun s => C s s s) - gibbsPairAverage w H (fun s x => C s s x) -
    gibbsPairAverage w H (fun s x => C s x s + C s x x) +
    2 * gibbsTripleAverage w H C

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorPrincipalObservables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The direct and fresh principal Ward observables retain only the spin
projection of the state. They therefore agree on every finite leaf cutoff. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {X : Type*}

def tensorOffDirect {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N))
    (sp : X → Spin N) (F : Spin N → Spin N → ℝ)
    (U : SpecialOrthogonal N) (σ : Fin 2 → X) : ℝ :=
  (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K,
    (offCoordinateVariation i j F (specialToOrthogonal U) (sp (σ 0), sp (σ 1)) +
      offCoordinateProduct i j F (specialToOrthogonal U) (sp (σ 0), sp (σ 1)) *
        ((eig i - eig j) * (coordinateProduct i j (specialToOrthogonal U) (sp (σ 0)) +
          coordinateProduct i j (specialToOrthogonal U) (sp (σ 1)))))

def tensorOffFresh {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N))
    (sp : X → Spin N) (F : Spin N → Spin N → ℝ)
    (U : SpecialOrthogonal N) (σ : Fin 3 → X) : ℝ :=
  (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K,
    offCoordinateProduct i j F (specialToOrthogonal U) (sp (σ 0), sp (σ 1)) *
      ((eig i - eig j) * coordinateProduct i j (specialToOrthogonal U) (sp (σ 2)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorDiagonalPrincipalObservables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The one- and two-replica principal observables for the diagonal Ward
identity, with a generic spin projection for countable leaf passage. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {X : Type*}

def tensorDiagonalDirect {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N))
    (sp : X → Spin N) (U : SpecialOrthogonal N) (σ : Fin 1 → X) : ℝ :=
  (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K,
    (spinCoordinate (specialToOrthogonal U) (sp (σ 0)) j ^ 2 -
      spinCoordinate (specialToOrthogonal U) (sp (σ 0)) i ^ 2 +
      coordinateProduct i j (specialToOrthogonal U) (sp (σ 0)) *
        ((eig i - eig j) * coordinateProduct i j (specialToOrthogonal U) (sp (σ 0))))

def tensorDiagonalFresh {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N))
    (sp : X → Spin N) (U : SpecialOrthogonal N) (σ : Fin 2 → X) : ℝ :=
  (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K,
    coordinateProduct i j (specialToOrthogonal U) (sp (σ 0)) *
      ((eig i - eig j) * coordinateProduct i j (specialToOrthogonal U) (sp (σ 1)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorGGRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete tensor GG rate tends to zero for every fixed monomial. -/

noncomputable section

open IsingPerceptron Filter
open scoped Topology BigOperators

namespace InvariantIsing

def tensorContactGGRate (N j m : ℕ) (L B : ℝ) : ℝ :=
  contactGGRate N j L B + 2 * B * (∑ a, (enumeratedSpectralDegree m j a : ℝ)) * diagonalContactRate N L

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralPartition
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
attribute [-simp] _root_.OAI.InvariantIsing.cavityGroupBlockOfBlock_view
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Total spin overlap and self normalization for a genuine spectral partition. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

lemma spectralPartition_spin_unit {m : ℕ} {Q : ProbabilityMeasure (SpectralArray (m + 1))}
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ)) :
    ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), spectralSpinArray x 0 1 ∈ Icc (0 : ℝ) 1 := by
  filter_upwards [hP, hn] with x hx hnx
  exact ⟨Finset.sum_nonneg (fun a _ => hnx a.castSucc), (le_abs_self _).trans (hx.1 0 1)⟩

lemma spectralLinearArray_spinWeight {m : ℕ} (x : SpectralArray (m + 1)) :
    spectralLinearArray (spectralSpinWeight m) x = spectralSpinArray x := by
  funext i j
  simp only [spectralLinearArray, spectralLinearEntry, Fin.sum_univ_castSucc,
    spectralSpinWeight, Fin.lastCases_castSucc, Fin.lastCases_last, one_mul, zero_mul, add_zero,
    spectralSpinArray]

lemma spectralLinearArray_single {m : ℕ} (a : Fin m) (x : SpectralArray m) :
    spectralLinearArray (Pi.single a 1) x = spectralCoordinateArray a x := by
  classical
  funext i j
  simp [spectralLinearArray, spectralLinearEntry, spectralCoordinateArray, Pi.single_apply]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralDiagonalWardLimits
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak closure of the one-replica diagonal Ward residual. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

def spectralDiagonalWardResidual {m : ℕ} (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (ρ eig : Fin m → ℝ) (a b : Fin m) : ℝ :=
  ρ a * (∫ x, (x (0,0) b.castSucc : ℝ) ∂(Q : Measure (SpectralArray (m + 1)))) -
  ρ b * (∫ x, (x (0,0) a.castSucc : ℝ) ∂(Q : Measure (SpectralArray (m + 1)))) +
  (eig a - eig b) * (∫ x, (x (0,0) a.castSucc : ℝ) * (x (0,0) b.castSucc : ℝ) -
    (x (0,1) a.castSucc : ℝ) * (x (0,1) b.castSucc : ℝ) ∂(Q : Measure (SpectralArray (m + 1))))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorArrayDiagonalWard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual enriched diagonal Ward bound is exactly the corresponding
spectral-array residual, retaining the common rotation in both replicas. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology NNReal

namespace InvariantIsing

def spectralDiagonalWardDirect {m : ℕ} (ρ eig : Fin m → ℝ) (a b : Fin m)
    (x : SpectralArray (m + 1)) : ℝ :=
  ρ a * (x (0,0) b.castSucc : ℝ) - ρ b * (x (0,0) a.castSucc : ℝ) +
    (eig a - eig b) * ((x (0,0) a.castSucc : ℝ) * (x (0,0) b.castSucc : ℝ))

def spectralDiagonalWardFresh {m : ℕ} (eig : Fin m → ℝ) (a b : Fin m)
    (x : SpectralArray (m + 1)) : ℝ :=
  (eig a - eig b) * ((x (0,1) a.castSucc : ℝ) * (x (0,1) b.castSucc : ℝ))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralWardLimits
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak closure of the spectral Ward residual, with converging block
proportions and eigenvalues. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

def spectralOffWardResidual {m : ℕ} (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (ρ eig : Fin m → ℝ) (a b : Fin m) (Φ : ℝ → ℝ) : ℝ :=
  ρ a * (∫ x, Φ (spectralSpinArray x 0 1) * (x (0,1) b.castSucc : ℝ) ∂(Q : Measure _)) -
  ρ b * (∫ x, Φ (spectralSpinArray x 0 1) * (x (0,1) a.castSucc : ℝ) ∂(Q : Measure _)) +
  (eig a - eig b) * (∫ x, Φ (spectralSpinArray x 0 1) *
    ((x (0,0) a.castSucc : ℝ) * (x (0,1) b.castSucc : ℝ) +
      (x (0,1) a.castSucc : ℝ) * (x (1,1) b.castSucc : ℝ) -
      2 * ((x (0,2) a.castSucc : ℝ) * (x (1,2) b.castSucc : ℝ))) ∂(Q : Measure _))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralWardAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The spectral off-diagonal residual as a direct minus fresh replica
expectation, matching the finite rotation calculation. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def spectralOffWardDirect {m : ℕ} (ρ eig : Fin m → ℝ) (a b : Fin m)
    (Φ : ℝ → ℝ) (x : SpectralArray (m + 1)) : ℝ :=
  Φ (spectralSpinArray x 0 1) *
    (ρ a * (x (0,1) b.castSucc : ℝ) - ρ b * (x (0,1) a.castSucc : ℝ) +
      (eig a - eig b) * ((x (0,0) a.castSucc : ℝ) * (x (0,1) b.castSucc : ℝ) +
        (x (0,1) a.castSucc : ℝ) * (x (1,1) b.castSucc : ℝ)))

def spectralOffWardFresh {m : ℕ} (eig : Fin m → ℝ) (a b : Fin m)
    (Φ : ℝ → ℝ) (x : SpectralArray (m + 1)) : ℝ :=
  (eig a - eig b) * Φ (spectralSpinArray x 0 1) *
    (x (0,2) a.castSucc : ℝ) * (x (1,2) b.castSucc : ℝ)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorArrayWard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enriched array laws satisfy the normalized spectral block Ward bound. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def spinPairOverlap {N : ℕ} (σ τ : Spin N) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, spinValue (σ i) * spinValue (τ i)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorContactRegion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The genuine compact parameter region for the finite upper comparison.
Field covariance increments are nonnegative and their sum is capped. -/

noncomputable section
open Set
open scoped BigOperators

namespace InvariantIsing

def tensorContactRegion (N m n : ℕ) (H : ℝ) : Set (TensorContactParameter N m n) :=
  Icc (0, (fun _ => 0), (fun _ => 1), (fun _ => 1))
    (1, (fun _ => H), (fun _ => 2), (fun _ => 2)) ∩
      {p | (∑ j, p.2.1 j) ≤ H}

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorFieldDerivative
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The right derivative of an independent linear-field insertion in the
tensor model. The variance-zero endpoint is included. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

def tensorFieldPairObservable {N n : ℕ} (g : ℕ → ℝ)
    (σ : Fin 2 → Spin N × LabeledLeaf n) : ℝ :=
  ((N : ℝ)⁻¹ * ∑ i, spinValue ((σ 1).1 i) * spinValue ((σ 0).1 i)) *
    g (labeledCommonDepth n (σ 1).2 (σ 0).2)


end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorFieldDerivativeIntegrability
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrability of the tensor pressure before varying its
linear field. Gaussian CGF bounds suffice; no concentration input is used. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

def tensorDeterministicEnergy {N : ℕ} (eig c : Fin N → ℝ) (n : ℕ)
    (ω : SpecialOrthogonal N × LabeledTree n) (x : Spin N × LabeledLeaf n) : ℝ :=
  rotatedEnergy eig (specialRotation ω.1) x.1 + fieldEnergy c x.1

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_PressureMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Almost-sure concentration of the actual pressure about its expectation. -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace InvariantIsing

/-- Deterministic reference obtained by removing the quadratic interaction. -/
def noninteractingPressure {N : ℕ} (c : Fin N → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * logPartition (fieldEnergy c)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_TailOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The upper-tail order used in the finite-spectrum upper comparison. -/

noncomputable section

open MeasureTheory Set

namespace InvariantIsing

def pathTail (p : OverlapPath) (s : ℝ) : ℝ := ∫ u in s..1, p u

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralQuantilePaths
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous pair quantile laws of the actual spectral GG limits. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Topology

namespace InvariantIsing

def spectralLinearLaw {m : ℕ} (Q : ProbabilityMeasure (SpectralArray m)) (w : Fin m → ℝ) : Measure ℝ :=
  (Q : Measure (SpectralArray m)).map (fun x => spectralLinearArray w x 0 1)

instance spectralLinearLaw_probability {m : ℕ} (Q : ProbabilityMeasure (SpectralArray m))
    (w : Fin m → ℝ) : IsProbabilityMeasure (spectralLinearLaw Q w) :=
  (Measure.isProbabilityMeasure_map_iff
    (by unfold spectralLinearArray spectralLinearEntry; fun_prop :
      Measurable (fun x : SpectralArray m => spectralLinearArray w x 0 1)).aemeasurable).mpr inferInstance

lemma spectralLinearLaw_unit {m : ℕ} (Q : ProbabilityMeasure (SpectralArray m)) (w : Fin m → ℝ)
    (hs : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), spectralLinearArray w x 0 1 ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ y ∂spectralLinearLaw Q w, y ∈ Icc (0 : ℝ) 1 := by
  exact (ae_map_iff (by unfold spectralLinearArray spectralLinearEntry; fun_prop :
    Measurable (fun x : SpectralArray m => spectralLinearArray w x 0 1)).aemeasurable
      measurableSet_Icc).mpr hs

def spectralQuantilePath {m : ℕ} (Q : ProbabilityMeasure (SpectralArray m)) (w : Fin m → ℝ)
    (hs : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), spectralLinearArray w x 0 1 ∈ Icc (0 : ℝ) 1) :
    InvariantIsing.OverlapPath where
  val := quantileFunction (spectralLinearLaw Q w)
  monotone := monotone_quantileFunction (spectralLinearLaw_unit Q w hs)
  nonneg s := (quantileFunction_mem (spectralLinearLaw_unit Q w hs) s).1
  le_one s := (quantileFunction_mem (spectralLinearLaw_unit Q w hs) s).2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralPartitionPaths
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual spectral-group quantiles sum to the total spin quantile. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma spectralCoordinate_unit {m : ℕ} {Q : ProbabilityMeasure (SpectralArray m)}
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), ∀ a, 0 ≤ (x (0,1) a : ℝ)) (a : Fin m) :
    ∀ᵐ x ∂(Q : Measure (SpectralArray m)),
      spectralLinearArray (Pi.single a 1) x 0 1 ∈ Icc (0 : ℝ) 1 := by
  filter_upwards [hn] with x hx
  rw [spectralLinearArray_single]
  exact ⟨hx a, (x (0,1) a).property.2⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorFieldTailBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The contact field directions are bounded continuous tests of the actual
spectral array, so their expectations pass to the synchronized limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

def spectralSpinDepthTail {m : ℕ} (n j : ℕ) (x : SpectralArray (m + 1)) : ℝ :=
  spectralSpinArray x 0 1 * depthTail n j (x (0,1) (Fin.last m) : ℝ)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorLeafTail
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar prefix test in the actual finite tensor model. The root is
averaged after the cascade marking identity. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Topology NNReal

namespace InvariantIsing

def tensorLeafPrefixTest {N n : ℕ} (d : Fin n)
    (σ : Fin 2 → Spin N × LabeledLeaf n) : ℝ :=
  if (labeledAddress n (σ 1).2).take (d + 1) =
    (labeledAddress n (σ 0).2).take (d + 1) then 1 else 0

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorZeroAmplitude
attribute [-instance] _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing zero-amplitude tensor marks

Projection onto the site coordinates sends the tensor Gaussian product law
to the original site-field law.  This identifies the actual zero-amplitude
cascade pressure with the unperturbed rotated enriched pressure.
-/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

def tensorSiteProjection {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (z : SpinTensorIndex I degree → ℝ) : Fin N → ℝ :=
  fun i => z (Sum.inl i)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiberFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tied overlap levels remain tied in an almost-everywhere limit. A
monotone factor through the overlap is then constructed explicitly;
no invertibility or absence of plateaus is assumed. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace InvariantIsing

def cavityFiberValues (p B : OverlapPath) (D : Set ℝ) (z : ℝ) : Set ℝ :=
  insert 0 (B.val '' {s | s ∈ D ∧ p s ≤ z})

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteDeficit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The deficit and cumulative masses of a genuine finite overlap
quantile, with atoms retained at all cell values. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace InvariantIsing

lemma finite_overlap_value_mem_unit {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (q : Fin (n + 1) → ℝ)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (j : Fin (n + 1)) : q j ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨s, hs⟩ := exists_between (hcut (Fin.castSucc_lt_succ (i := j)))
  rw [← hp j s hs]
  exact ⟨p.nonneg s, p.le_one s⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianRows
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian rows used to generate the finite fresh frames. Their empirical
Gram matrices converge almost surely to the identity at fixed frame width. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal

namespace InvariantIsing

instance instIsProbabilityMeasureForallFinRealCavityGaussianRow (q : ℕ) : IsProbabilityMeasure (cavityGaussianRow q) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin q => gaussianReal 0 1)))

instance instIsProbabilityMeasureForallNatForallFinRealCavityGaussianRows (q : ℕ) : IsProbabilityMeasure (cavityGaussianRows q) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => cavityGaussianRow q)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGroupGaussian
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent Gaussian arrays for the finitely many spectral groups.
The finite restrictions are exactly standard Gaussian vectors. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InvariantIsing

instance instIsProbabilityMeasureForallFinForallNatForallRealCavityGroupGaussianRows (m q : ℕ) : IsProbabilityMeasure (cavityGroupGaussianRows m q) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin m => cavityGaussianRows q)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-spectrum interaction energy and its monotonicity. -/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

def finiteSpectralSlope (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (x : ℝ) : ℝ :=
  ∑ a, eig a * projectedResolventDerivative ρ eig hρ hρsum a x

def finiteThermalScalar (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (t x : ℝ) : ℝ :=
  x * finiteR ρ eig hρ hρsum (t * x)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSpinTransition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar physical-spin transition and its bounded martingale
properties, including degenerate covariance increments. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldSpinTransition_square_le (ζ : ℝ) (v : ℝ≥0) {F a : ℝ → ℝ}
    (hF : Measurable F) (hgrowth : HasLinearGrowth F) (ha : Measurable a)
    {B : ℝ} (haB : ∀ u, |a u| ≤ B) (z : ℝ) :
    (fieldSpinTransition ζ v F a z) ^ 2 ≤
      fieldSpinTransition ζ v F (fun u => (a u) ^ 2) z := by
  have hw := integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hgrowth ζ
  have : IsProbabilityMeasure ((gaussianReal z v).tilted (fun u => ζ * F u)) :=
    MeasureTheory.isProbabilityMeasure_tilted hw
  have hm : MemLp a 2 ((gaussianReal z v).tilted (fun u => ζ * F u)) :=
    MemLp.of_bound ha.aestronglyMeasurable B
      (Filter.Eventually.of_forall (fun u => by simpa only [Real.norm_eq_abs] using haB u))
  have hv := variance_nonneg a ((gaussianReal z v).tilted (fun u => ζ * F u))
  rw [variance_eq_sub hm] at hv
  change 0 ≤ fieldSpinTransition ζ v F (fun u => (a u) ^ 2) z -
    (fieldSpinTransition ζ v F a z) ^ 2 at hv
  linarith

lemma fieldSpinTransition_mono_test (ζ : ℝ) (v : ℝ≥0) (F : ℝ → ℝ)
    {a b : ℝ → ℝ} (ha : Measurable a) (hb : Measurable b) {A B : ℝ}
    (haB : ∀ u, |a u| ≤ A) (hbB : ∀ u, |b u| ≤ B)
    (hab : ∀ u, a u ≤ b u) (z : ℝ) :
    fieldSpinTransition ζ v F a z ≤ fieldSpinTransition ζ v F b z := by
  exact integral_mono
    (Integrable.of_bound ha.aestronglyMeasurable A
      (Filter.Eventually.of_forall (fun u => by simpa only [Real.norm_eq_abs] using haB u)))
    (Integrable.of_bound hb.aestronglyMeasurable B
      (Filter.Eventually.of_forall (fun u => by simpa only [Real.norm_eq_abs] using hbB u))) hab

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldVectorSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual vector spin sampling for independent scalar cavity fields. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators NNReal

namespace InvariantIsing

instance fieldVectorTransitionKernel_markov (N : ℕ) (ζ : ℝ) (v : ℝ≥0)
    (F : ℝ → ℝ) (hF : Measurable F) :
    IsMarkovKernel (fieldVectorTransitionKernel N ζ v F hF) :=
  ⟨fun _ => inferInstanceAs (IsProbabilityMeasure (Measure.pi _))⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldPublishedEvaluation
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evaluating the finite published endpoint law on physical spin means. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldEndpointCoordinateTest (N : ℕ) (h : FieldStep)
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N)
    (p : ℕ × ((Fin N → ℝ) × (Fin N → ℝ))) : ℝ :=
  Φ (q (fieldDepthLevel h p.1)) * (Real.tanh (p.2.1 j) * Real.tanh (p.2.2 j))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralProjectionMass
attribute [-instance] _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Haar-averaged squared projections are constant within each eigenspace.
This follows from the finite coordinate Ward identity and holds for any
fixed nonzero nonnegative spin prior, including deterministic fields. -/

noncomputable section
open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def meanCoordinateSquare {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    (w : Spin N → ℝ) (eig c : Fin N → ℝ) (i : Fin N) : ℝ :=
  ∫ U, gibbsAverage w (orbitHamiltonian eig c (specialToOrthogonal U))
    (fun σ => spinCoordinate (specialToOrthogonal U) σ i ^ 2) ∂μ

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralPermutation
attribute [-instance] _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral reorderings can be realized inside SO(N). A single row sign
corrects a permutation determinant without changing any squared projection. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Matrix

namespace InvariantIsing

lemma permutationMatrix_det_sq {N : ℕ} (p : Equiv.Perm (Fin N)) :
    (p.permMatrix ℝ).det ^ 2 = 1 := by
  let U : Orthogonal N := ⟨p.permMatrix ℝ, permutationMatrix_orthogonal p⟩
  rcases orthogonal_det_eq_one_or_neg_one U with h | h <;>
    change (p.permMatrix ℝ).det = _ at h <;> rw [h] <;> norm_num

lemma permutationSignDiagonal_sq {N : ℕ} (hN : 0 < N) (p : Equiv.Perm (Fin N)) :
    permutationSignDiagonal hN p * (permutationSignDiagonal hN p)ᵀ = 1 := by
  rw [permutationSignDiagonal, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    split_ifs
    · exact (pow_two ((p.permMatrix ℝ).det)).symm.trans (permutationMatrix_det_sq p)
    · norm_num
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

/-- A permutation of spectral coordinates, with determinant corrected to one. -/
def spectralPermutation {N : ℕ} (hN : 0 < N) (p : Equiv.Perm (Fin N)) :
    SpecialOrthogonal N :=
  ⟨permutationSignDiagonal hN p * p.permMatrix ℝ, by
    apply Matrix.mem_specialOrthogonalGroup_iff.mpr
    constructor
    · apply (Matrix.mem_orthogonalGroup_iff (Fin N) ℝ).mpr
      rw [Matrix.transpose_mul]
      calc
        _ = permutationSignDiagonal hN p *
            (p.permMatrix ℝ * (p.permMatrix ℝ)ᵀ) * (permutationSignDiagonal hN p)ᵀ := by
          simp only [Matrix.mul_assoc]
        _ = permutationSignDiagonal hN p * (permutationSignDiagonal hN p)ᵀ := by
          rw [(Matrix.mem_orthogonalGroup_iff (Fin N) ℝ).mp (permutationMatrix_orthogonal p)]
          simp
        _ = 1 := permutationSignDiagonal_sq hN p
    · rw [Matrix.det_mul, permutationSignDiagonal_det, ← pow_two, permutationMatrix_det_sq]⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PriorSpinLeafConditioning
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conditional independent spin sampling for a finite constrained prior.
The prior is retained in both its terminal and its conditional spin kernels. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators ENNReal NNReal

namespace InvariantIsing

def priorSpinLeafTerminal {N n : ℕ} (μ : Measure (Spin N)) [IsProbabilityMeasure μ] (H : Spin N × LabeledLeaf n → ℝ) (α : LabeledLeaf n) : ℝ :=
  finiteLogIntegral μ (fun σ => H (σ, α))

def priorSpinLeafPairResidualKernel {N n : ℕ} (μ : Measure (Spin N)) [IsProbabilityMeasure μ] (H : Spin N × LabeledLeaf n → ℝ) :
    Kernel (Fin 2 → LabeledLeaf n) (Fin 2 → Spin N) :=
  ⟨fun α => Measure.pi (fun i : Fin 2 =>
      gibbsProbability μ (fun σ => H (σ, α i))),
    measurable_of_countable _⟩

instance priorSpinLeafPairResidualKernel_markov {N n : ℕ} (μ : Measure (Spin N)) [IsProbabilityMeasure μ] (H : Spin N × LabeledLeaf n → ℝ) :
    IsMarkovKernel (priorSpinLeafPairResidualKernel μ H) :=
  ⟨fun _ => inferInstanceAs (IsProbabilityMeasure (Measure.pi _))⟩

def priorSpinLeafPairJoin {N n : ℕ}
    (p : (Fin 2 → LabeledLeaf n) × (Fin 2 → Spin N)) : Fin 2 → Spin N × LabeledLeaf n :=
  fun i => (p.2 i, p.1 i)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinGroupProjection
attribute [-instance] _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A nearest projection to all group constraints at once. Its number of
changed spins is exactly the sum of the group count discrepancies. -/

noncomputable section
open scoped BigOperators symmDiff

namespace InvariantIsing

lemma exists_spin_group_projection {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (k : A → ℕ) (hk : ∀ a, k a ≤ spinGroupSize group a) (σ : Spin N) :
    ∃ τ ∈ spinGroupSlice group k,
      hammingDist σ τ = ∑ a, ((spinGroupCount group σ a - k a) +
        (k a - spinGroupCount group σ a)) := by
  classical
  let S := fun a => Finset.univ.filter (fun i => group i = a)
  let P := fun a => Finset.univ.filter (fun i => group i = a ∧ σ i = true)
  have hPS (a : A) : P a ⊆ S a := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.1⟩
  choose T hT hcard hdist using fun a => exists_subset_card_nearest (P a) (S a) (hPS a) (k a) (hk a)
  let τ : Spin N := fun i => decide (i ∈ T (group i))
  have hTa {a : A} {i : Fin N} (hi : i ∈ T a) : group i = a :=
    (Finset.mem_filter.mp (hT a hi)).2
  have hcount (a : A) : spinGroupCount group τ a = k a := by
    have he : (Finset.univ.filter fun i => group i = a ∧ τ i = true) = T a := by
      ext i
      by_cases hi : group i = a
      · simp [τ, hi]
      · have hn : i ∉ T a := fun hm => hi (hTa hm)
        simp [hi, hn]
    exact (congrArg Finset.card he).trans (hcard a)
  refine ⟨τ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcount⟩, ?_⟩
  let D := Finset.univ.filter (fun i => σ i ≠ τ i)
  have he (a : A) : D.filter (fun i => group i = a) = P a ∆ T a := by
    ext i
    by_cases hi : group i = a
    · cases hσ : σ i <;> simp [D, P, τ, hi, hσ, Finset.mem_symmDiff]
    · have hn : i ∉ T a := fun hm => hi (hTa hm)
      simp [D, P, hi, hn, Finset.mem_symmDiff]
  change D.card = _
  rw [Finset.card_eq_sum_card_fiberwise (s := D) (t := Finset.univ)
    (f := group) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro a _
  rw [he, hdist]
  rfl

def spinGroupProjection {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (k : A → ℕ) (hk : ∀ a, k a ≤ spinGroupSize group a)
    (σ : Spin N) : Spin N := Classical.choose (exists_spin_group_projection group k hk σ)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldAffineRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite scalar log-cosh recursion with affine covariance
increments is a smooth field family on its strict covariance interval. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldLogCoshFamily (I : Set ℝ) : FieldSmoothFamily I where
  U := fun p => Real.log (Real.cosh p.2)
  X := fun p => Real.tanh p.2
  XX := fun p => 1 / (Real.cosh p.2) ^ 2
  T := fun _ => 0
  KX := 1
  KXX := 1
  KT := 0
  mU := by fun_prop
  mX := by
    have ht : Measurable (fun x : ℝ => Real.tanh x) := by
      simp only [Real.tanh_eq]
      fun_prop
    exact ht.comp measurable_snd
  mXX := by fun_prop
  mT := measurable_const
  bX := fun p => field_abs_tanh_le_one p.2
  bXX := fun p => field_tanh_second_bound p.2
  bT := fun _ _ => by simp
  derivative := fun p _ => by
    have h : HasDerivAt (fun x => Real.log (Real.cosh x)) (Real.tanh p.2) p.2 := by
      simpa only [Real.tanh_eq_sinh_div_cosh] using
        (Real.hasDerivAt_cosh p.2).log (Real.cosh_pos p.2).ne'
    have hs : HasFDerivAt (fun q : ℝ × ℝ => q.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
      hasFDerivAt_snd
    convert (config := {transparency := .instances, preTransparency := .instances}) h.hasFDerivAt.comp p hs using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro q
      simp [pairLinear, mul_comm]
  spatial := fun _ y => by
    simpa only [Real.tanh_eq_sinh_div_cosh] using
      (Real.hasDerivAt_cosh y).log (Real.cosh_pos y).ne'
  second := fun _ y => field_hasDerivAt_tanh y

def fieldAffineValue : List FieldAffineStep → ℝ × ℝ → ℝ
  | [], p => Real.log (Real.cosh p.2)
  | av :: L, p => gaussianTransform (av.base + av.slope * p.1) av.exponent
      (fun y => fieldAffineValue L (p.1, y)) p.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldCoordinateDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact single-height derivatives of the finite Gaussian field value.
An interior height changes its two adjacent covariance increments with
opposite signs. The final height includes the diagonal subtraction. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

def fieldFixedAffine (S : List (ℝ × ℝ≥0)) : List FieldAffineStep :=
  S.map fun av => ⟨av.2, 0, av.1⟩

lemma fieldFixedAffine_base (S : List (ℝ × ℝ≥0))
    (hS : ∀ av ∈ S, 0 < (av.2 : ℝ)) :
    ∀ av ∈ fieldFixedAffine S, 0 < av.base := by
  intro av hav
  obtain ⟨bv, hb, rfl⟩ := List.mem_map.mp hav
  exact hS bv hb

lemma fieldFixedAffine_slope (S : List (ℝ × ℝ≥0)) :
    ∀ av ∈ fieldFixedAffine S, av.slope = 0 := by
  intro av hav
  obtain ⟨bv, _, rfl⟩ := List.mem_map.mp hav
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticStationaryFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed terminal potential as an actual two-coordinate family.
This permits use of the established affine Gaussian differentiation theorem
for the inverse-coordinate time comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def magneticStationaryFamily (I : Set ℝ) (F : ℝ → ℝ) (P : MagneticContinuationJet)
    (hF : Measurable F) (K L : ℝ) (bK : ∀ z, |P.value z| ≤ K)
    (bL : ∀ z, |P.first z| ≤ L) (dF : ∀ z, HasDerivAt F (P.value z) z) :
    FieldSecondFamily I where
  U := fun p => F p.2
  X := fun p => P.value p.2
  XX := fun p => P.first p.2
  T := fun _ => 0
  KX := K
  KXX := L
  KT := 0
  mU := hF.comp measurable_snd
  mX := P.mValue.comp measurable_snd
  mXX := P.mFirst.comp measurable_snd
  mT := measurable_const
  bX := fun p => bK p.2
  bXX := fun p => bL p.2
  bT := fun _ _ => by simp
  derivative := fun p _ => by
    convert (config := {transparency := .instances, preTransparency := .instances}) (dF p.2).hasFDerivAt.comp p hasFDerivAt_snd using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro q
      simp [pairLinear, mul_comm]
  spatial := fun _ => dF
  second := fun _ => P.dValue
  TX := fun _ => 0
  TT := fun _ => 0
  KTX := 0
  KTT := 0
  mTX := measurable_const
  mTT := measurable_const
  bTX := fun _ _ => by simp
  bTT := fun _ _ => by simp
  derivativeX := fun p _ => by
    convert (config := {transparency := .instances, preTransparency := .instances}) (P.dValue p.2).hasFDerivAt.comp p hasFDerivAt_snd using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro q
      simp [pairLinear, mul_comm]
  derivativeT := fun p _ => by
    convert hasFDerivAt_const (0 : ℝ) p using 1
    all_goals try with_reducible_and_instances rfl
    apply ContinuousLinearMap.ext
    intro q
    simp [pairLinear]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticContinuationTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint variance/spatial differentiation of the actual scalar
continuation. The covariance differential is left as integrals here;
Gaussian integration by parts then identifies its time generator. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

def magneticGaussianAverageDifferential (ζ v : ℝ) (F M A B : ℝ → ℝ) (z : ℝ) :
    (ℝ × ℝ) →L[ℝ] ℝ :=
  let ν := (gaussianReal 0 1).tilted (fun u => ζ * F (z + Real.sqrt v * u))
  let D := fun u => pairLinear
    (M (z + Real.sqrt v * u) * ((1 / (2 * Real.sqrt v)) * u))
    (M (z + Real.sqrt v * u))
  (∫ u, pairLinear
      (B (z + Real.sqrt v * u) * ((1 / (2 * Real.sqrt v)) * u))
      (B (z + Real.sqrt v * u)) + (ζ * A (z + Real.sqrt v * u)) • D u ∂ν) -
    (∫ u, A (z + Real.sqrt v * u) ∂ν) • (∫ u, ζ • D u ∂ν)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticGaussianCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar-coordinate form of the actual joint Gaussian continuation
differential. All integrability is supplied by bounded finite-spin jets. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def magneticGaussianSpace (ζ v : ℝ) (F M A B : ℝ → ℝ) (z : ℝ) : ℝ :=
  gaussianTiltAverage v ζ F B z + ζ *
    (gaussianTiltAverage v ζ F (fun y => A y * M y) z -
      gaussianTiltAverage v ζ F A z * gaussianTiltAverage v ζ F M z)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticContinuationGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact heat generator of the scalar continuation. Integration by
parts removes the apparent inverse square-root singularity from the
positive-variance differential. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def magneticGaussianGenerator (ζ v : ℝ) (F M Q A B C : ℝ → ℝ) (z : ℝ) : ℝ :=
  let T := fun f => gaussianTiltAverage v ζ F f z
  T C / 2 + ζ * T (fun y => B y * M y) +
    ζ / 2 * (T (fun y => A y * Q y) - T A * T Q) +
    ζ ^ 2 / 2 * (T (fun y => A y * (M y) ^ 2) - T A * T (fun y => (M y) ^ 2))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticWeightedJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial derivatives of q²Hᵤᵤ. Multiplying by q² removes the first-order
term from the differentiated inverse-coordinate continuation equation. -/

noncomputable section

namespace InvariantIsing

def magneticWeightedJetValue (P A : MagneticContinuationFourJet) (z : ℝ) : ℝ :=
  A.second z - A.first z * P.second z / P.first z

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinHammingBall
attribute [-instance] _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential bounds for Hamming balls and for the fibers of a
nearest-slice map. The bound is uniform over the target configuration. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def spinHammingBall {N : ℕ} (τ : Spin N) (d : ℕ) : Finset (Spin N) :=
  Finset.univ.filter (fun σ => hammingDist σ τ ≤ d)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldProjectionLoss
attribute [-instance] _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A depth-free terminal loss estimate for the actual constrained
partition function. It separates the field second moment from the
expected number of flips, before any Gaussian-path averaging. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace InvariantIsing

def fieldProjectionDistance {N : ℕ} (f : Spin N → Spin N) (z : Fin N → ℝ) : ℝ :=
  ∑ σ, finiteCanonicalWeights (fieldEnergy z) σ * (hammingDist σ (f σ) : ℝ)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical pressure on a fixed spin constraint, retaining its original
cube mass. The Haar Lipschitz constant is independent of the constraint. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def restrictedRotatedPressure {N : ℕ} (S : Finset (Spin N))
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * restrictedSpinLog S (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PriorFrozenReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Freezing one actual Gaussian perturbation coordinate with a fixed prior. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

def priorFrozenLaw {N : ℕ} (μ : Measure (SpecialOrthogonal N)) (j : ℕ) :
    Measure (PriorFrozenData N j) := μ.prod (otherNamespacesLaw (j+1))

instance priorFrozenLaw_probability {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsProbabilityMeasure μ] (j : ℕ) : IsProbabilityMeasure (priorFrozenLaw μ j) := by
  unfold priorFrozenLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def priorFrozenInsertion {N : ℕ} (j : ℕ) (p : PriorFrozenData N j × (ℕ → ℝ)) :
    SpecialOrthogonal N × (ℕ → ℝ) :=
  (p.1.1,gaussianNamespaceJoin (j+1) (p.2,p.1.2))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralBallQuantizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite quantizer attached to the null-boundary ball cover. -/

noncomputable section
open MeasureTheory Set Metric
open scoped Topology Classical Function

namespace InvariantIsing

def spectralBallQuantizer {n : ℕ} (c r : Fin n → ℝ) (fallback : ℝ) (x : ℝ) : ℝ :=
  (spectralPartitionIndex (spectralBallCell (fun i => ball (c i) (r i)))
    (spectralBallCell_cover _) x).elim fallback c

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldRefineIncrements
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A one-cut refinement inserts exactly one zero covariance increment. -/

noncomputable section
open IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldNNIncrement (h : FieldStep) (i : Fin (h.depth + 1)) : ℝ × ℝ≥0 :=
  ((fieldIncrement h i).1, NNReal.mk (fieldIncrement h i).2 (fieldIncrement_nonneg h i))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldFiniteFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint finite-height derivative data for the scalar Ising recursion.
Only the covariance coordinates required by a finite subdivision occur. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

def fieldFiniteLogCosh (n : ℕ) (I : Set (Fin n → ℝ)) : FieldFiniteFamily n I where
  U := fun p => Real.log (Real.cosh p.2)
  X := fun p => Real.tanh p.2
  XX := fun p => 1 / Real.cosh p.2 ^ 2
  P := fun _ _ => 0
  PX := fun _ _ => 0
  PP := fun _ _ _ => 0
  KX := 1
  KXX := 1
  KP := 0
  KPX := 0
  KPP := 0
  kx_nonneg := by norm_num
  kxx_nonneg := by norm_num
  kp_nonneg := by norm_num
  kpx_nonneg := by norm_num
  kpp_nonneg := by norm_num
  mU := by fun_prop
  mX := by
    have hm : Measurable Real.tanh := by
      have he : Real.tanh = fun x : ℝ => Real.sinh x / Real.cosh x := by
        funext x
        exact Real.tanh_eq_sinh_div_cosh x
      rw [he]
      fun_prop
    exact hm.comp measurable_snd
  mXX := by fun_prop
  mP := fun _ => measurable_const
  mPX := fun _ => measurable_const
  mPP := fun _ _ => measurable_const
  bX := fun p _ => field_abs_tanh_le_one p.2
  bXX := fun p _ => field_tanh_second_bound p.2
  bP := fun _ _ _ => by simp
  bPX := fun _ _ _ => by simp
  bPP := fun _ _ _ _ => by simp
  derivative := fun p _ => by
    have h := ((Real.hasDerivAt_cosh p.2).log (Real.cosh_pos p.2).ne').hasFDerivAt.comp p
      hasFDerivAt_snd
    convert (config := {transparency := .instances, preTransparency := .instances}) h using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro q
      simp [Real.tanh_eq_sinh_div_cosh, mul_comm]
  derivativeX := fun p _ => by
    have h := (field_hasDerivAt_tanh p.2).hasFDerivAt.comp p hasFDerivAt_snd
    convert (config := {transparency := .instances, preTransparency := .instances}) h using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro q
      simp [mul_comm]
  derivativeP := fun _ p _ => by
    convert hasFDerivAt_const (0 : ℝ) p using 1
    all_goals try with_reducible_and_instances rfl
    apply ContinuousLinearMap.ext
    intro q
    simp
  symmetric := fun _ _ _ _ => rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldFiniteRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closure of the finite scalar Ising recursion under joint height and
spatial derivatives. The Hessian symmetry is part of the constructed data. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

def fieldFiniteValue {n : ℕ} : List (FieldFiniteStep n) → FieldCovariate n → ℝ
  | [], p => Real.log (Real.cosh p.2)
  | av :: L, p => gaussianTransform (fieldFiniteVariance av.base av.slope p.1)
      av.exponent (fun y => fieldFiniteValue L (p.1, y)) p.2

def fieldFiniteFamily {n : ℕ} (I : Set (Fin n → ℝ)) (hI : IsOpen I)
    (V R D : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) :
    (L : List (FieldFiniteStep n)) →
      (∀ av ∈ L, ∀ t ∈ I, 0 < fieldFiniteVariance av.base av.slope t ∧
        fieldFiniteVariance av.base av.slope t ≤ V) →
      (∀ av ∈ L, ∀ t ∈ I, ∀ i, |fieldFiniteSlope av.base av.slope t i| ≤ R) →
      (∀ av ∈ L, ∀ t ∈ I, ∀ i j, |fieldFiniteCurvature av.base av.slope t i j| ≤ D) →
      FieldFiniteFamily n I
  | [], _, _, _ => fieldFiniteLogCosh n I
  | av :: L, hL, hc, hd =>
      (fieldFiniteFamily I hI V R D hR hD L
        (fun bv hb => hL bv (List.mem_cons_of_mem av hb))
        (fun bv hb => hc bv (List.mem_cons_of_mem av hb))
        (fun bv hb => hd bv (List.mem_cons_of_mem av hb))).transform hI av.base av.slope av.exponent
          V R D hR hD (fun t ht => (hL av List.mem_cons_self t ht).1)
          (fun t ht => (hL av List.mem_cons_self t ht).2)
          (hc av List.mem_cons_self) (hd av List.mem_cons_self)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightUpdate
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the finite covariance charts with literal updates
of a field height. The formula is defined without choosing proofs of the
order constraints; whenever the updated heights are admissible it is the
original `fieldValue` of that field. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldHeightIncrement_eq (h : FieldStep) (j : Fin (h.depth + 1)) :
    fieldHeightIncrement h.height j = (fieldIncrement h j).2 := rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightJoint
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal field-height chart as a finite joint affine covariance
recursion. No admissibility proof is built into this chart. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators NNReal

namespace InvariantIsing

def fieldHeightFiniteStep (h : FieldStep) (j : Fin (h.depth + 1)) : FieldFiniteStep (h.depth + 1) where
  base := 0
  slope := fieldHeightSlope j
  exponent := h.cut j.castSucc

def fieldHeightFiniteList (h : FieldStep) : List (FieldFiniteStep (h.depth + 1)) :=
  List.ofFn (fieldHeightFiniteStep h)

def fieldHeightJointValue (h : FieldStep) (r : Fin (h.depth + 1) → ℝ) (z : ℝ) : ℝ :=
  fieldFiniteValue (fieldHeightFiniteList h) (r, z) - r (Fin.last h.depth) / 2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightInteriorLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual interior-height magnetization as the root average of the
adjacent Gaussian variation family. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

def fieldInteriorPrefix (h : FieldStep) (j : Fin h.depth) : List (ℝ × ℝ≥0) :=
  (scalarFieldIncrements h).take (j.val - 1)

def fieldInteriorTail (h : FieldStep) (j : Fin h.depth) : List (ℝ × ℝ≥0) :=
  (scalarFieldIncrements h).drop (j.val + 1)

lemma scalarFieldIncrements_strict (h : FieldStep)
    (hstrict : ∀ i, 0 < (fieldIncrement h i).2) :
    ∀ av ∈ scalarFieldIncrements h, 0 < (av.2 : ℝ) := by
  intro av hav
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hav
  exact hstrict i.succ

lemma fieldInteriorTail_strict (h : FieldStep) (j : Fin h.depth)
    (hstrict : ∀ i, 0 < (fieldIncrement h i).2) :
    ∀ av ∈ fieldInteriorTail h j, 0 < (av.2 : ℝ) := by
  intro av hav
  exact scalarFieldIncrements_strict h hstrict av (List.mem_of_mem_drop hav)

lemma fieldInteriorPrefix_length (h : FieldStep) (j : Fin h.depth) :
    (fieldInteriorPrefix h j).length = j.val - 1 := by
  simp only [fieldInteriorPrefix, List.length_take, scalarFieldIncrements_length]
  exact Nat.min_eq_left (by omega)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightInteriorOrder
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
attribute [-simp] _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual mixed-height order for nonterminal coordinates. The unchanged
root has exponent zero and is integrated only after the positive prefix. -/

noncomputable section
open IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldHeight_update_interior_mem (h : FieldStep)
    (hstrict : ∀ i, 0 < (fieldIncrement h i).2) (j : Fin h.depth) (t : ℝ)
    (ht : t ∈ Ioo (-(fieldIncrement h j.castSucc).2) (fieldIncrement h j.succ).2) :
    Function.update h.height j.castSucc (h.height j.castSucc + t) ∈ fieldStrictHeightCone h.depth := by
  classical
  intro k
  rw [fieldHeightIncrement_update]
  by_cases hk : k = j.castSucc
  · subst k
    simp only [ite_true, if_true, fieldHeightIncrement_eq]
    linarith [ht.1]
  · by_cases hl : k.val = j.castSucc.val + 1
    · have hkj : k = j.succ := by apply Fin.ext; simpa using hl
      subst k
      simp only [hk, ite_false, if_false, Fin.val_succ, Fin.val_castSucc, ite_true, if_true,
        fieldHeightIncrement_eq]
      linarith [ht.2]
    · simpa only [hk, hl, ite_false, if_false, add_zero, fieldHeightIncrement_eq] using hstrict k

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightFinalOrder
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The final-height version of the actual mixed-coordinate order. -/

noncomputable section
open IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

def fieldFinalPrefix (h : FieldStep) : List (ℝ × ℝ≥0) :=
  (scalarFieldIncrements h).take (h.depth - 1)

lemma fieldHeight_update_final_mem (h : FieldStep)
    (hstrict : ∀ i, 0 < (fieldIncrement h i).2) (t : ℝ)
    (ht : t ∈ Ioi (-(fieldIncrement h (Fin.last h.depth)).2)) :
    Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + t) ∈
      fieldStrictHeightCone h.depth := by
  classical
  intro k
  rw [fieldHeightIncrement_update]
  by_cases hk : k = Fin.last h.depth
  · subst k
    simp only [ite_true, if_true, fieldHeightIncrement_eq]
    have ht' : -(fieldIncrement h (Fin.last h.depth)).2 < t := ht
    linarith
  · have hn : k.val ≠ (Fin.last h.depth).val + 1 := by
      simp only [Fin.val_last]
      omega
    simpa only [hk, hn, ite_false, if_false, add_zero, fieldHeightIncrement_eq] using hstrict k

lemma fieldFinalPrefix_length (h : FieldStep) :
    (fieldFinalPrefix h).length = h.depth - 1 := by
  simp only [fieldFinalPrefix, List.length_take, scalarFieldIncrements_length]
  exact Nat.min_eq_left (by omega)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldVaryingRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed finite cascade exponents with varying nonnegative scalar
variances. These are the actual log-cosh recursion and spin observables. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldVaryingValue {E : Type*} (L : List (ℝ × (E → ℝ≥0))) (t : E) : ℝ → ℝ :=
  L.foldr (fun av F => gaussianOperator av.1 (av.2 t) F) (fun z => Real.log (Real.cosh z))

def fieldVaryingMean {E : Type*} : List (ℝ × (E → ℝ≥0)) → E → ℝ → ℝ
  | [], _ => Real.tanh
  | av :: L, t => fieldSpinTransition av.1 (av.2 t) (fieldVaryingValue L t)
      (fieldVaryingMean L t)

def fieldVaryingSquares {E : Type*} : (L : List (ℝ × (E → ℝ≥0))) → E →
    Fin (L.length + 1) → ℝ → ℝ
  | [], _ => fun _ z => (Real.tanh z) ^ 2
  | av :: L, t => Fin.cons (fun z => (fieldVaryingMean (av :: L) t z) ^ 2)
      (fun i => fieldSpinTransition av.1 (av.2 t) (fieldVaryingValue L t)
        (fieldVaryingSquares L t i))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightRegularization
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded strict-height approximation of an arbitrary finite field.
Every variance increment is increased by the same small scalar. -/

noncomputable section
open IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

def fieldRegularizedHeight (h : FieldStep) (t : ℝ) (i : Fin (h.depth + 1)) : ℝ :=
  h.height i + fieldHeightEpsilon t * (i.val + 1 : ℕ)

def fieldRegularizedIncrements (h : FieldStep) : List (ℝ × (ℝ → ℝ≥0)) :=
  List.ofFn (fun i : Fin h.depth => ((fieldIncrement h i.succ).1,
    fun t => NNReal.mk ((fieldIncrement h i.succ).2 + fieldHeightEpsilon t)
      (add_nonneg (fieldIncrement_nonneg h i.succ) (fieldHeightEpsilon_nonneg t))))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightBoundaryContinuity
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The strict regularization converges in the actual field value and
every actual magnetization level. No endpoint derivative is used. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped NNReal Topology

namespace InvariantIsing

def fieldRegularizedRoot (h : FieldStep) (t : ℝ) : ℝ≥0 :=
  NNReal.mk (h.height 0 + fieldHeightEpsilon t)
    (add_nonneg (h.nonneg 0) (fieldHeightEpsilon_nonneg t))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldEnergyCoordinates
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual scalar-field forest as a finite Ising energy-mark forest. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma measurable_fieldEnergy_map (N : ℕ) : Measurable (fieldEnergy (N := N)) := by
  unfold fieldEnergy
  fun_prop

def fieldEnergyMarkLaw (N : ℕ) (v : ℝ≥0) : ProbabilityMeasure (Spin N → ℝ) :=
  (vectorGaussianLaw N v).map (measurable_fieldEnergy_map N).aemeasurable

def fieldEnergyCoordinates (N : ℕ) (h : FieldStep)
    (p : LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ)) :
    LabeledTree h.depth × (ForestVertex h.depth → Spin N → ℝ) :=
  (p.1, fun a => fieldEnergy (p.2 a))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralArrayEnergy
attribute [-instance] _root_.OAI.InvariantIsing.spectralLinearLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The interaction before temperature multiplication is an exact bounded
continuous spectral-array observable, so its Gibbs mean passes to weak limits. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

def spectralArrayInteractionEnergy {m : ℕ} (lam : Fin m → ℝ)
    (x : SpectralArray (m + 1)) : ℝ :=
  (1 / 2 : ℝ) * ∑ a, lam a * (x (0,0) a.castSucc : ℝ)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_OffsetFieldPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact field contributions in repeated blocks following a zero-field prefix. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology
namespace InvariantIsing

def offsetBlockField {n : ℕ} (r K : ℕ) (b : Fin n → ℝ) : Fin (r+K*n) → ℝ :=
  Fin.addCases (fun _ => 0) (consecutiveBlockField K b)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_FiniteFieldLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite field populations admit exact block templates and canonical
all-dimensional labels with the corresponding limiting proportions. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace InvariantIsing

def countedFieldGroup {A : Type*} [Fintype A] {N : ℕ} (s : A → ℕ)
    (hs : ∑ a, s a=N) : Fin N → A :=
  let E := Fintype.equivFin A
  fun i => E.symm (cavityOrderedGroup (fun j => s (E.symm j))
    ((Equiv.sum_comp E.symm s).trans hs) i)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_CanonicalOrthogonalLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete orthogonal Haar probability from the square Gaussian frame.
This determines the orthogonal orbit law in the Wishart corollary. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
namespace InvariantIsing

def squareFrameOrthogonal {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) : Orthogonal N :=
  if h : Aᵀ*A=1 then ⟨A,(Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mpr h⟩ else 1

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SimpleFieldData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A simple random field is represented using only its positive-mass values. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Classical
namespace InvariantIsing

variable {Ω : Type*} [MeasurableSpace Ω]

instance simpleFieldPositive_nonempty (P : Measure Ω) [IsProbabilityMeasure P]
    (s : SimpleFunc Ω ℝ) : Nonempty (SimpleFieldPositive P s) := by
  obtain ⟨i,hi⟩ := exists_pos_spectral_weight (fun _ => measureReal_nonneg) (simpleFieldWeight_sum P s)
  exact ⟨⟨i,hi⟩⟩

def simpleFieldPositiveIndex (P : Measure Ω) [IsProbabilityMeasure P] (s : SimpleFunc Ω ℝ) :
    Ω → SimpleFieldPositive P s :=
  positiveSpectralLabel (simpleFieldWeight P s) (Classical.choice inferInstance) ∘ simpleFieldIndex s

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldQuantizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite field quantizers with null boundaries and a uniform tail bound. -/
noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology Classical
namespace InvariantIsing

def fieldBallSimple {n : ℕ} (c r : Fin n → ℝ) : SimpleFunc ℝ ℝ := by
  let : MeasurableSpace (Option (Fin n)) := ⊤
  exact (SimpleFunc.ofFinite (fun i : Option (Fin n) => i.elim 0 c)).comp
    (spectralPartitionIndex (spectralBallCell (fun i => ball (c i) (r i))) (spectralBallCell_cover _))
    (measurable_spectralPartitionIndex _ (spectralBallCell_cover _) (spectralBallCell_disjoint _)
      (spectralBallCell_measurable _ (fun _ => measurableSet_ball)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PhysicalFieldPermutation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A deterministic permutation of field sites preserves the physical Haar mean. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix
namespace InvariantIsing

def fieldSitePermutation {N : ℕ} (p : Equiv.Perm (Fin N)) : Orthogonal N :=
  ⟨p.permMatrix ℝ, permutationMatrix_orthogonal p⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PriorFieldLogNormalizer
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logarithmic field normalizers for a deterministic finite spin prior,
with joint root/forest integrability proved from the actual recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

def priorFieldVectorLogNormalizer (N : ℕ) (π : Measure (Spin N)) [IsProbabilityMeasure π] (h : FieldStep) (z : Fin N → ℝ)
    (p : LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ)) : ℝ :=
  Real.log (∫ s : Spin N × LabeledLeaf h.depth,
    Real.exp (fieldEnergy (fieldVectorEndpoint N h p z s.2) s.1)
      ∂(π.prod (labeledLeafLaw h.depth p.1)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SeedForestPairData
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A pair of ancestor-generated paths on the independent uniform forest. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing
variable {ι : Type}

def seedForestPairData (n : ℕ)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ)) (z : ι → ℝ)
    (q : (ℕ → LabeledLeaf n) × MarkForest unitInterval n) :
    ℕ × (Fin n → (ι → ℝ) × (ι → ℝ)) :=
  (labeledCommonDepth n (q.1 0) (q.1 1),fun i =>
    (cascadeSeedPath n ψ z q.2 (q.1 0) i,cascadeSeedPath n ψ z q.2 (q.1 1) i))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SeedPairStep
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability of one pair of root updates with both descendant paths. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing
variable {ι : Type}

def seedPairStep (n : ℕ) (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (z₁ z₂ : ι → ℝ) (α β : LabeledLeaf n)
    (F : (Fin (n+1) → (ι → ℝ) × (ι → ℝ)) → ℝ)
    (p : (unitInterval × unitInterval) × (MarkForest unitInterval n × MarkForest unitInterval n)) : ℝ :=
  F (Fin.cons (ψ 0 z₁ p.1.1,ψ 0 z₂ p.1.2) (fun i =>
    (cascadeSeedPath n (fun j => ψ (j+1)) (z₁+ψ 0 z₁ p.1.1) p.2.1 α i,
     cascadeSeedPath n (fun j => ψ (j+1)) (z₂+ψ 0 z₂ p.1.2) p.2.2 β i)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPairSubGaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The independent canonical site-pair law supplies the dimension-sharp
concentration bound needed in constrained magnetic replacement. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

def spinPairSiteValue (p : Bool × Bool) : ℝ := spinValue p.1 * spinValue p.2

def spinPairSiteSum {N : ℕ} (u : Fin N → Bool × Bool) : ℝ := ∑ j, spinPairSiteValue (u j)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_VectorGaussianTransition
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual vector Gaussian transition for a nonseparable terminal,
including constrained spin blocks. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal BigOperators

namespace InvariantIsing

instance vectorShiftGaussianKernel_markov (N : ℕ) (v : ℝ≥0) :
    IsMarkovKernel (vectorShiftGaussianKernel N v) := by
  unfold vectorShiftGaussianKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance vectorGaussianTransition_markov (N : ℕ) (a : ℝ) (v : ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) :
    IsMarkovKernel (vectorGaussianTransition N a v F hF) :=
  ⟨fun _ => normalizeMass_probability _⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_VectorTerminalCascade
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ancestor kernels for the two finite-dimensional Gaussian field terminals. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal ENNReal
namespace InvariantIsing

def vectorTerminalBackward (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (i : ℕ) : (Fin N → ℝ) → ℝ :=
  backwardValue n b (fun j => vectorGaussianLaw N (v j)) (fun _ p => p.1+p.2) F i

def vectorTerminalMultiplier (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (i : ℕ) (p : (Fin N → ℝ) × (Fin N → ℝ)) : ℝ :=
  Real.exp (vectorTerminalBackward N n b v F (i+1) (vectorTerminalUpdate N n i p) -
    vectorTerminalBackward N n b v F i p.1)

lemma measurable_vectorTerminalBackward (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (i : ℕ) :
    Measurable (vectorTerminalBackward N n b v F i) :=
  measurable_backwardValue n b _ (fun _ => measurable_fst.add measurable_snd) hF i

lemma measurable_vectorTerminalMultiplier (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (i : ℕ) :
    Measurable (vectorTerminalMultiplier N n b v F i) :=
  (((measurable_vectorTerminalBackward N n b v F hF (i+1)).comp
    (measurable_vectorTerminalUpdate N n i)).sub
    ((measurable_vectorTerminalBackward N n b v F hF i).comp measurable_fst)).exp

def vectorTerminalAncestorKernel (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (i : ℕ) :
    Kernel (Fin N → ℝ) (Fin N → ℝ) :=
  ⟨fun z => (vectorGaussianLaw N (v i) : Measure (Fin N → ℝ)).withDensity
    (fun a => ENNReal.ofReal (vectorTerminalMultiplier N n b v F i (z,a)^b i)),
    measurable_random_withDensity (ν := fun _ => (vectorGaussianLaw N (v i) : Measure (Fin N → ℝ)))
      (W := fun p => ENNReal.ofReal (vectorTerminalMultiplier N n b v F i p^b i))
      measurable_const ((measurable_vectorTerminalMultiplier N n b v F hF i).pow_const (b i)).ennreal_ofReal⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_VectorTerminalLabeled
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Original labeled Gibbs laws for finite Gaussian vector terminals. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

def vectorTerminalCoordinateLaw (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) : Measure (VectorTerminalCoordinates N n) :=
  (labeledCascadeLaw n b : Measure (LabeledTree n)).prod
    (Measure.infinitePi fun a : ForestVertex n => (vectorGaussianLaw N (v (forestVertexDepth n a)) : Measure (Fin N → ℝ)))

instance vectorTerminalCoordinateLaw_probability (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) :
    IsProbabilityMeasure (vectorTerminalCoordinateLaw N n b v) := by
  unfold vectorTerminalCoordinateLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def vectorLabeledTerminalLaw (N n : ℕ) (F : (Fin N → ℝ) → ℝ)
    (z : Fin N → ℝ) (p : VectorTerminalCoordinates N n) : Measure (LabeledLeaf n) :=
  gibbsProbability (labeledLeafLaw n p.1)
    (fun α => F (labeledEnergy n (markForestOfCoords (Fin N → ℝ) n p.2) α z))

instance vectorLabeledTerminalLaw_probability (N n : ℕ) (F : (Fin N → ℝ) → ℝ)
    (z : Fin N → ℝ) (p : VectorTerminalCoordinates N n) :
    IsProbabilityMeasure (vectorLabeledTerminalLaw N n F z p) := by
  unfold vectorLabeledTerminalLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma measurable_vectorLabeledTerminalLaw (N n : ℕ) (F : (Fin N → ℝ) → ℝ) (hF : Measurable F)
    (z : Fin N → ℝ) : Measurable (vectorLabeledTerminalLaw N n F z) := by
  unfold vectorLabeledTerminalLaw
  apply measurable_gibbsProbability (ν := fun p : VectorTerminalCoordinates N n => labeledLeafLaw n p.1)
    (H := fun p : VectorTerminalCoordinates N n × LabeledLeaf n =>
      F (labeledEnergy n (markForestOfCoords (Fin N → ℝ) n p.1.2) p.2 z))
    ((measurable_labeledLeafLaw n).comp measurable_fst)
  apply measurable_from_prod_countable_left
  intro α
  exact hF.comp ((measurable_labeledEnergy n α).comp
    (((measurable_markForestOfCoords _ n).comp measurable_snd).prodMk measurable_const))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_VectorPairIntegral
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The proved two-path formula for a finite Gaussian vector terminal. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

def vectorTerminalPairMean (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (z : Fin N → ℝ)
    (Φ : ℕ × (Fin n → (Fin N → ℝ) × (Fin N → ℝ)) → ℝ) : ℝ :=
  ∫ p : VectorTerminalCoordinates N n,
    referenceReplicaMean (labeledLeafLaw n p.1)
      (fun α => F (labeledEnergy n (markForestOfCoords (Fin N → ℝ) n p.2) α z))
      (fun σ : Fin 2 → LabeledLeaf n => Φ
        (labeledCommonDepth n (σ 0) (σ 1),fun i => (p.2 (edgeAt n (σ 0) i),p.2 (edgeAt n (σ 1) i))))
      ∂vectorTerminalCoordinateLaw N n b v

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_ZeroFieldPopulations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vanishing field populations can be relabeled into a positive population. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators Classical
namespace InvariantIsing

def positiveFieldProjection {A : Type*} (γ : A → ℝ) (fallback : {a // 0 < γ a}) (a : A) : A :=
  (positiveSpectralLabel γ fallback a).val

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianGramResolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive real resolvent of the physical Gaussian Gram matrix. -/
noncomputable section
open Matrix
namespace InvariantIsing

def gaussianGramResolvent {N m : ℕ} (t : ℝ)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) : Matrix (Fin N) (Fin N) ℝ :=
  (t • (1 : Matrix (Fin N) (Fin N) ℝ)+gaussianPatternCoupling 1 z)⁻¹

def gaussianGramStieltjes {N m : ℕ} (t : ℝ)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) : ℝ := (gaussianGramResolvent t z).trace/N

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianGramEmpiricalTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the physical matrix resolvent with the empirical spectral transform. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
namespace InvariantIsing

lemma positiveResolventTest_bound {t : ℝ} (ht : 0 < t) (x : ℝ) :
    0 ≤ positiveResolventTest t x ∧ positiveResolventTest t x ≤ 1/t := by
  have hd : 0 < t+max x 0 := add_pos_of_pos_of_nonneg ht (le_max_right x 0)
  exact ⟨(one_div_pos.mpr hd).le,one_div_le_one_div_of_le ht (le_add_of_nonneg_right (le_max_right x 0))⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GordonCurveMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiation under the finite Gaussian minimum--maximum interpolation. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing
variable {U V : Type*} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]

def gordonCurveMean {d : ℕ} (C A : U × V → Fin d → ℝ) (t : ℝ) : ℝ :=
  ∫ g, gordonValue (fun x => linearGaussian (cavityGaussianCurve C A t) g x)
    ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1)

def gordonCurveSlope {d : ℕ} (C A : U × V → Fin d → ℝ) (t : ℝ) : ℝ :=
  ∫ g, gordonMean (fun x => linearGaussian (cavityGaussianCurve C A t) g x)
    (fun x => linearGaussian (cavityGaussianCurveDerivative C A t) g x)
    ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarCompactness
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactness and entry bounds for the actual special orthogonal group. -/
noncomputable section
open Matrix Set
open scoped BigOperators
namespace InvariantIsing

lemma specialOrthogonal_entry_bound {N : ℕ} (U : SpecialOrthogonal N) (i j : Fin N) :
    |(U : Matrix (Fin N) (Fin N) ℝ) i j| ≤ 1 := by
  have hU := (Matrix.mem_orthogonalGroup_iff (Fin N) ℝ).mp
    (Matrix.mem_specialOrthogonalGroup_iff.mp U.property).1
  have hrow : (∑ k, ((U : Matrix (Fin N) (Fin N) ℝ) i k)^2) = 1 := by
    simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply_eq,pow_two]
      using congrFun (congrFun hU i) i
  have hs : ((U : Matrix (Fin N) (Fin N) ℝ) i j)^2 ≤ 1 := by
    rw [← hrow]
    exact Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  exact (sq_le_one_iff_abs_le_one _).mp hs

lemma isCompact_specialOrthogonal (N : ℕ) :
    IsCompact (Matrix.specialOrthogonalGroup (Fin N) ℝ : Set (Matrix (Fin N) (Fin N) ℝ)) := by
  have hb : IsCompact (Set.pi Set.univ fun _ : Fin N =>
      Set.pi Set.univ fun _ : Fin N => Set.Icc (-1 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  apply hb.of_isClosed_subset (isClosed_specialOrthogonal N)
  intro A hA
  simp only [Set.mem_pi,Set.mem_univ,forall_true_left,Set.mem_Icc]
  intro i j
  exact abs_le.mp (specialOrthogonal_entry_bound ⟨A,hA⟩ i j)

instance specialOrthogonal_compactSpace (N : ℕ) : CompactSpace (SpecialOrthogonal N) :=
  isCompact_iff_compactSpace.mp (isCompact_specialOrthogonal N)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial Laplacian on the orthogonal group commutes with rotations. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

/-- Ordered coordinate planes; its carré du champ is the sum of the ordered squares. -/
def haarPolynomialLaplacian (N : ℕ) : Module.End ℝ (MatrixPolynomial N) :=
  ∑ i, ∑ j, matrixPolynomialOperator (planeGenerator i j)*
    matrixPolynomialOperator (planeGenerator i j)

lemma haarPolynomialLaplacian_apply {N : ℕ} (p : MatrixPolynomial N) :
    haarPolynomialLaplacian N p = ∑ i : Fin N, ∑ j : Fin N,
      matrixPolynomialDerivation (planeGenerator i j)
        (matrixPolynomialDerivation (planeGenerator i j) p) := by
  simp only [haarPolynomialLaplacian,LinearMap.sum_apply,Module.End.mul_apply,
    matrixPolynomialOperator_apply]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite polynomial spaces, padded by the constant atom, for the rotation semigroup. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

instance haarPolynomialSpace_finite (N d : ℕ) : Module.Finite ℝ (haarPolynomialSpace N d) :=
  Module.Finite.span_of_finite ℝ (Set.finite_range _)

lemma haarPolynomialWord_mem {N d : ℕ} (w : Fin d → Option (Fin N × Fin N)) :
    haarPolynomialWord w ∈ haarPolynomialSpace N d :=
  Submodule.subset_span ⟨w,rfl⟩

lemma haarPolynomialWord_cons {N d : ℕ} (a : Option (Fin N × Fin N))
    (w : Fin d → Option (Fin N × Fin N)) :
    haarPolynomialWord (Fin.cons a w) = haarPolynomialAtom a*haarPolynomialWord w := by
  simp only [haarPolynomialWord,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]

lemma haarPolynomialSpace_atom_mul {N d : ℕ} (a : Option (Fin N × Fin N))
    {p : MatrixPolynomial N} (hp : p ∈ haarPolynomialSpace N d) :
    haarPolynomialAtom a*p ∈ haarPolynomialSpace N (d+1) := by
  refine Submodule.span_induction (p := fun q _ =>
    haarPolynomialAtom a*q ∈ haarPolynomialSpace N (d+1)) ?_ ?_ ?_ ?_ hp
  · intro q hq
    rcases hq with ⟨w,rfl⟩
    rw [← haarPolynomialWord_cons]
    exact haarPolynomialWord_mem _
  · simpa only [mul_zero] using (haarPolynomialSpace N (d+1)).zero_mem
  · intro p q _ _ hp hq
    rw [mul_add]
    exact (haarPolynomialSpace N (d+1)).add_mem hp hq
  · intro c p _ hp
    rw [mul_smul_comm]
    exact (haarPolynomialSpace N (d+1)).smul_mem c hp

lemma one_mem_haarPolynomialSpace (N d : ℕ) :
    (1 : MatrixPolynomial N) ∈ haarPolynomialSpace N d := by
  simpa only [haarPolynomialWord,haarPolynomialAtom,Finset.prod_const_one] using
    haarPolynomialWord_mem (N := N) (d := d) (fun _ => none)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialInvariantSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite polynomial spaces are invariant under every rotation derivative. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

lemma haarPolynomialDerivation_word_mem {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (d : ℕ)
    (w : Fin d → Option (Fin N × Fin N)) :
    matrixPolynomialDerivation A (haarPolynomialWord w) ∈ haarPolynomialSpace N d := by
  induction d with
  | zero =>
    simp [haarPolynomialWord]
  | succ d ih =>
    rw [← Fin.cons_self_tail w,haarPolynomialWord_cons,Derivation.leibniz]
    simp only [smul_eq_mul]
    apply (haarPolynomialSpace N (d+1)).add_mem
    · exact haarPolynomialSpace_atom_mul (w 0) (ih (Fin.tail w))
    · cases h : w 0 with
      | none => simp [haarPolynomialAtom]
      | some ij =>
        rcases ij with ⟨i,j⟩
        simp only [haarPolynomialAtom,matrixPolynomialDerivation_X,Finset.mul_sum]
        apply (haarPolynomialSpace N (d+1)).sum_mem
        intro k _
        rw [mul_smul_comm]
        apply (haarPolynomialSpace N (d+1)).smul_mem
        simpa only [haarPolynomialAtom,mul_comm] using
          haarPolynomialSpace_atom_mul (some (k,j)) (haarPolynomialWord_mem (Fin.tail w))

lemma haarPolynomialDerivation_mem {N d : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) {p : MatrixPolynomial N}
    (hp : p ∈ haarPolynomialSpace N d) :
    matrixPolynomialDerivation A p ∈ haarPolynomialSpace N d := by
  refine Submodule.span_induction (p := fun q _ =>
    matrixPolynomialDerivation A q ∈ haarPolynomialSpace N d) ?_ ?_ ?_ ?_ hp
  · intro q hq
    rcases hq with ⟨w,rfl⟩
    exact haarPolynomialDerivation_word_mem A d w
  · simpa only [map_zero] using (haarPolynomialSpace N d).zero_mem
  · intro p q _ _ hp hq
    rw [map_add]
    exact (haarPolynomialSpace N d).add_mem hp hq
  · intro c p _ hp
    rw [Derivation.map_smul]
    exact (haarPolynomialSpace N d).smul_mem c hp

lemma haarPolynomialLaplacian_mem {N d : ℕ} {p : MatrixPolynomial N}
    (hp : p ∈ haarPolynomialSpace N d) :
    haarPolynomialLaplacian N p ∈ haarPolynomialSpace N d := by
  rw [haarPolynomialLaplacian_apply]
  apply (haarPolynomialSpace N d).sum_mem
  intro i _
  apply (haarPolynomialSpace N d).sum_mem
  intro j _
  exact haarPolynomialDerivation_mem _ (haarPolynomialDerivation_mem _ hp)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialHeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A genuine finite-dimensional heat flow on each invariant polynomial space. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

def haarPolynomialCoordinates (N d : ℕ) :
    haarPolynomialSpace N d ≃ₗ[ℝ] HaarPolynomialCoordinates N d :=
  (Module.finBasis ℝ (haarPolynomialSpace N d)).equivFun

def haarPolynomialRestrictedLaplacian (N d : ℕ) :
    Module.End ℝ (haarPolynomialSpace N d) :=
  (haarPolynomialLaplacian N).restrict (fun _ hp => haarPolynomialLaplacian_mem hp)

def haarPolynomialCoordinateLaplacian (N d : ℕ) :
    HaarPolynomialCoordinates N d →L[ℝ] HaarPolynomialCoordinates N d :=
  ((haarPolynomialCoordinates N d).toLinearMap.comp
    ((haarPolynomialRestrictedLaplacian N d).comp
      (haarPolynomialCoordinates N d).symm.toLinearMap)).toContinuousLinearMap

def haarPolynomialHeat (N d : ℕ) (t : ℝ) :
    Module.End ℝ (haarPolynomialSpace N d) :=
  (haarPolynomialCoordinates N d).symm.toLinearMap.comp
    ((NormedSpace.exp (t • haarPolynomialCoordinateLaplacian N d)).toLinearMap.comp
      (haarPolynomialCoordinates N d).toLinearMap)

def haarPolynomialCoordinateEval {N d : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) :
    HaarPolynomialCoordinates N d →L[ℝ] ℝ :=
  ((matrixPolynomialEval M).toLinearMap.comp
    ((haarPolynomialSpace N d).subtype.comp
      (haarPolynomialCoordinates N d).symm.toLinearMap)).toContinuousLinearMap

@[simp] lemma haarPolynomialCoordinateEval_apply {N d : ℕ}
    (M : Matrix (Fin N) (Fin N) ℝ) (p : haarPolynomialSpace N d) :
    haarPolynomialCoordinateEval M (haarPolynomialCoordinates N d p) =
      matrixPolynomialEval M (p : MatrixPolynomial N) := by
  simp [haarPolynomialCoordinateEval]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarHeatLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiating linear observables of the finite polynomial heat flow. -/
noncomputable section
open Matrix MvPolynomial
namespace InvariantIsing

def haarPolynomialLinearCoordinates {N d : ℕ} (F : MatrixPolynomial N →ₗ[ℝ] ℝ) :
    HaarPolynomialCoordinates N d →L[ℝ] ℝ :=
  (F.comp ((haarPolynomialSpace N d).subtype.comp
    (haarPolynomialCoordinates N d).symm.toLinearMap)).toContinuousLinearMap

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialGamma
attribute [-instance] _root_.OAI.InvariantIsing.haarPolynomialSpace_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product and second-order identities for the actual polynomial rotation operator. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

def haarPolynomialGamma {N : ℕ} (p q : MatrixPolynomial N) : MatrixPolynomial N :=
  ∑ i, ∑ j, matrixPolynomialDerivation (planeGenerator i j) p*
    matrixPolynomialDerivation (planeGenerator i j) q

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarHeatContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint continuity of the finite polynomial heat flow. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

def haarPolynomialBasis (N d : ℕ)
    (i : Fin (Module.finrank ℝ (haarPolynomialSpace N d))) : MatrixPolynomial N :=
  ((Module.finBasis ℝ (haarPolynomialSpace N d)) i : MatrixPolynomial N)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarFunctionalCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sum of squared Lie brackets, with the precise dimension factor. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

def planeFunctionalMatrix {N : ℕ}
    (ell : Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => ell (planeGenerator i j)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialCurvature
attribute [-instance] _root_.OAI.InvariantIsing.haarPolynomialSpace_finite
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialCoordinateEval_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The curvature inequality for polynomial observables, proved by finite algebra. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

def matrixPolynomialDifferential {N : ℕ}
    (p : MatrixPolynomial N) (M : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] ℝ where
  toFun A := matrixPolynomialEval M (matrixPolynomialDerivation A p)
  map_add' A B := by simp
  map_smul' c A := by simp [Derivation.smul_apply]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarLogCurvature
attribute [-instance] _root_.OAI.InvariantIsing.haarPolynomialSpace_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The pointwise curvature inequality with a logarithmic gradient correction. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

def haarGradientValue {N : ℕ} (p : MatrixPolynomial N)
    (M : Matrix (Fin N) (Fin N) ℝ) (a : Fin N × Fin N) : ℝ :=
  matrixPolynomialEval M (matrixPolynomialDerivation (planeGenerator a.1 a.2) p)

def haarHessianValue {N : ℕ} (p : MatrixPolynomial N)
    (M : Matrix (Fin N) (Fin N) ℝ) (a b : Fin N × Fin N) : ℝ :=
  matrixPolynomialEval M (matrixPolynomialDerivation (planeGenerator b.1 b.2)
    (matrixPolynomialDerivation (planeGenerator a.1 a.2) p))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarLogBarrier
attribute [-instance] _root_.OAI.InvariantIsing.haarPolynomialSpace_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The pointwise minimum inequality for a logarithmic heat-gradient barrier. -/
noncomputable section
open Matrix MvPolynomial
namespace InvariantIsing

def haarLogBarrier {N : ℕ} (p : MatrixPolynomial N) (a : ℝ) : MatrixPolynomial N :=
  a • p^2-haarPolynomialGamma p p

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarHeatLogBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Time differentiation and continuity of the logarithmic gradient barrier. -/
noncomputable section
open Matrix MvPolynomial
namespace InvariantIsing

def haarHeatLogBarrier {N d : ℕ} (p : haarPolynomialSpace N d) (C t : ℝ) : MatrixPolynomial N :=
  haarLogBarrier ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N)
    (C*Real.exp (-2*((N:ℝ)-2)*t))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_RotationMatrix
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.specialPlaneRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix coordinates for Euclidean isometries and hyperplane reflections. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

@[simp] lemma rotationMatrix_specialRotation {N : ℕ} (U : SpecialOrthogonal N) :
    rotationMatrix (specialRotation U) = (U : Matrix (Fin N) (Fin N) ℝ) := by
  ext i j
  rw [rotationMatrix_apply,specialRotation_apply]
  simp only [PiLp.single_apply,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]

lemma rotationMatrix_reflection_apply {N : ℕ} (v : EuclideanSpace ℝ (Fin N))
    (i j : Fin N) :
    rotationMatrix (hyperplaneReflection v) i j =
      (1 : Matrix (Fin N) (Fin N) ℝ) i j-2*v i*v j/‖v‖^2 := by
  rw [rotationMatrix_apply,hyperplaneReflection_apply]
  simp only [PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,
    EuclideanSpace.inner_single_right,PiLp.single_apply,starRingEnd_apply,
    star_trivial,one_mul]
  rw [Matrix.one_apply]
  split_ifs <;> ring

lemma rotationMatrix_reflection_det {N : ℕ} (v : EuclideanSpace ℝ (Fin N)) (hv : v ≠ 0) :
    Matrix.det (rotationMatrix (hyperplaneReflection v)) = -1 := by
  rw [rotationMatrix,LinearMap.det_toMatrix,hyperplaneReflection,Submodule.det_reflection,
    Submodule.orthogonal_orthogonal,finrank_span_singleton hv,pow_one]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_ReflectionSegment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonsingular interpolation of reflection normals. -/
noncomputable section
open Matrix Set
open scoped BigOperators
namespace InvariantIsing

lemma reflectionNormalSegment_hasDerivAt {N : ℕ}
    (v w : EuclideanSpace ℝ (Fin N)) (t : ℝ) (i : Fin N) :
    HasDerivAt (fun s => reflectionNormalSegment v w s i) (w i-v i) t := by
  have h := (((hasDerivAt_const t 1).sub (hasDerivAt_id t)).mul_const (v i)).add
    ((hasDerivAt_id t).mul_const (w i))
  refine h.congr_deriv (Eq.symm ?_)
  · simp only [zero_sub,one_mul,neg_mul]
    ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_ReflectionSegmentDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entry derivatives along a nonsingular interpolation of reflection normals. -/
noncomputable section
open Matrix Set
open scoped BigOperators
namespace InvariantIsing

def reflectionSegmentMatrix {N : ℕ} (v w : EuclideanSpace ℝ (Fin N)) (t : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  rotationMatrix (hyperplaneReflection (reflectionNormalSegment v w t))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_ReflectionPairCurve
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A genuine special-orthogonal curve for a pair of hyperplane reflections. -/
noncomputable section
open Matrix Set Filter
open scoped BigOperators Topology
namespace InvariantIsing

def reflectionPair {N : ℕ} (v w : EuclideanSpace ℝ (Fin N))
    (hv : v ≠ 0) (hw : w ≠ 0) : SpecialOrthogonal N :=
  ⟨rotationMatrix (hyperplaneReflection v)*rotationMatrix (hyperplaneReflection w),
    Matrix.mem_specialOrthogonalGroup_iff.mpr
      ⟨(Matrix.orthogonalGroup (Fin N) ℝ).mul_mem (rotationMatrix_mem _) (rotationMatrix_mem _),
        by rw [Matrix.det_mul,rotationMatrix_reflection_det v hv,
          rotationMatrix_reflection_det w hw]; norm_num⟩⟩

def reflectionPairCurve {N : ℕ} (v w : EuclideanSpace ℝ (Fin N))
    (hw : w ≠ 0) (t : ℝ) : SpecialOrthogonal N :=
  if h : reflectionNormalSegment v w t ≠ 0 then
    reflectionPair (reflectionNormalSegment v w t) w h hw else 1

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarExponentialPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive polynomial truncations of an exponential observable. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

def haarExpPolynomial {N : ℕ} (n : ℕ) (p : MatrixPolynomial N) : MatrixPolynomial N :=
  ∑ k ∈ Finset.range (n+1), ((Nat.factorial k : ℝ)⁻¹) • p^k

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarGroupTopology
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual matrix-group topology and positivity of finite Haar measure. -/
noncomputable section
open Matrix MeasureTheory
namespace InvariantIsing

instance specialOrthogonal_topologicalGroup (N : ℕ) :
    IsTopologicalGroup (SpecialOrthogonal N) where
  continuous_mul := continuous_mul
  continuous_inv := by
    apply Continuous.subtype_mk
    change Continuous (fun U : SpecialOrthogonal N =>
      (U : Matrix (Fin N) (Fin N) ℝ).transpose)
    fun_prop

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialKernel
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite polynomial averaging kernels on the actual special orthogonal group. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory
open scoped BigOperators
namespace InvariantIsing

def haarKernelAtom {N : ℕ} (V : SpecialOrthogonal N) : Option (Fin N × Fin N) → ℝ
  | none => N
  | some ij => (V : Matrix (Fin N) (Fin N) ℝ) ij.1 ij.2

def haarKernelBase {N : ℕ} (U V : SpecialOrthogonal N) : ℝ :=
  N + ∑ i, ∑ j, (U : Matrix (Fin N) (Fin N) ℝ) i j *
    (V : Matrix (Fin N) (Fin N) ℝ) i j

def haarKernelAverage {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    (f : SpecialOrthogonal N → ℝ) (n : ℕ) : MatrixPolynomial N :=
  ∑ w : Fin n → Option (Fin N × Fin N),
    (∫ V, f V * ∏ k, haarKernelAtom V (w k) ∂μ) • haarPolynomialWord w

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarKernelConvolution
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Haar convolution by a positive polynomial kernel preserves Lipschitz constants. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Set
open scoped BigOperators
namespace InvariantIsing

def haarKernelMass {N : ℕ} (μ : Measure (SpecialOrthogonal N)) (n : ℕ) : ℝ :=
  ∫ V, (haarKernelBase 1 V)^n ∂μ

def haarKernelApprox {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    (f : SpecialOrthogonal N → ℝ) (n : ℕ) : MatrixPolynomial N :=
  (haarKernelMass μ n)⁻¹ • haarKernelAverage μ f n

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_SpecialSkewRotation
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.rotationMatrix_specialRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponentiating an arbitrary real skew matrix in the physical group. -/
noncomputable section
open Matrix
open scoped Matrix Matrix.Norms.Frobenius
namespace InvariantIsing

def skewRotation {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.transpose = -A) (t : ℝ) : Orthogonal N :=
  ⟨NormedSpace.exp (t • A), NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (by
    rw [skewAdjoint.mem_iff]
    simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial,
      star_smul,star_trivial,smul_neg] using congrArg (fun M => t • M) hA)⟩

lemma skewRotation_det {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.transpose = -A) (t : ℝ) :
    (skewRotation A hA t : Matrix (Fin N) (Fin N) ℝ).det = 1 := by
  let f : ℝ → ℝ := fun s => (skewRotation A hA s : Matrix (Fin N) (Fin N) ℝ).det
  have hc : Continuous f := by
    apply Continuous.matrix_det
    exact continuous_iff_continuousAt.mpr fun s =>
      (hasDerivAt_exp_smul_const' A s).continuousAt
  have hm : Set.MapsTo f Set.univ ({1,-1} : Set ℝ) := by
    intro s _
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff,f] using
      orthogonal_det_eq_one_or_neg_one (skewRotation A hA s)
  have he := isPreconnected_univ.constant_of_mapsTo
    (Set.toFinite ({1,-1} : Set ℝ)).isDiscrete hc.continuousOn hm (Set.mem_univ t)
      (Set.mem_univ (0:ℝ))
  simpa only [f,skewRotation,zero_smul,NormedSpace.exp_zero,Matrix.det_one] using he

def specialSkewRotation {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.transpose = -A) (t : ℝ) : SpecialOrthogonal N :=
  ⟨(skewRotation A hA t).val,Matrix.mem_specialOrthogonalGroup_iff.mpr
    ⟨(skewRotation A hA t).property,skewRotation_det A hA t⟩⟩

@[simp] lemma specialSkewRotation_zero {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.transpose = -A) : specialSkewRotation A hA 0 = 1 := by
  apply Subtype.ext
  simp [specialSkewRotation,skewRotation]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_ResolventMeasureUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive resolvents determine probability measures on the nonnegative real line. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace InvariantIsing

def resolventUnit (x : ℝ) : Icc (0 : ℝ) 1 :=
  ⟨positiveResolventTest 1 x, (positiveResolventTest_bound (t := 1) (by norm_num) x).1,
    by simpa only [one_div_one] using (positiveResolventTest_bound (t := 1) (by norm_num) x).2⟩

end InvariantIsing

end

end OAI
end



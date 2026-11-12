-- Prove2me | Definitions.Def_OAIQ258001
-- name    : OAIQ258001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T05:11:17.282436+00:00
-- url     : https://prove2.me/theorems/1008aed3-89e5-4fd4-b5f3-dfe6a65a0ecb
-- title:
--   Definitions bundle OAIQ258001 of the split of OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 452 declarations of OpenAI's Lean: 268 definitions, 4 inductive types or structures, 11 instances and 169 theorems. The definitions and types are `OAI.InvariantIsing.GaussianLipschitzVarianceInput`, `OAI.InvariantIsing.HaarDifferentiableCurve`, `OAI.InvariantIsing.HaarDifferentiableCurve.constant`, `OAI.InvariantIsing.HaarDifferentiableCurve.mul`, `OAI.InvariantIsing.HaarPolynomialCoordinates`, `OAI.InvariantIsing.MagneticContinuationBound`, `OAI.InvariantIsing.MagneticContinuationFourJet`, `OAI.InvariantIsing.MagneticContinuationFourJet.slope`, `OAI.InvariantIsing.MagneticContinuationFourJet.square`, `OAI.InvariantIsing.MagneticContinuationJet`, `OAI.InvariantIsing.MagneticContinuationJet.mul`, `OAI.InvariantIsing.MagneticContinuationJet.slopeTwoJet`, `OAI.InvariantIsing.MagneticContinuationJet.square`, `OAI.InvariantIsing.MagneticContinuationJet.toTwoJet`, `OAI.InvariantIsing.MagneticContinuationTwoJet`, `OAI.InvariantIsing.MagneticSlabBound`, `OAI.InvariantIsing.MagneticUniformBound`, `OAI.InvariantIsing.MatrixPolynomial`, `OAI.InvariantIsing.PriorFrozenData`, `OAI.InvariantIsing.ScaledLabelSimple`, `OAI.InvariantIsing.SpecialOrthogonal`, `OAI.InvariantIsing.SpectralArray`, `OAI.InvariantIsing.SpectralBlock`, `OAI.InvariantIsing.SpectralEntry`, `OAI.InvariantIsing.SpectralGram`, `OAI.InvariantIsing.SpectralPartitionGeometry`, `OAI.InvariantIsing.TensorContactParameter`, `OAI.InvariantIsing.TensorFlatDisorder`, `OAI.InvariantIsing.TensorFrozenData`, `OAI.InvariantIsing.UnitVector`, `OAI.InvariantIsing.VectorTerminalCoordinates`, `OAI.InvariantIsing.affineGaussianCoefficients`, `OAI.InvariantIsing.affineGaussianMean`, `OAI.InvariantIsing.affineGaussianSlope`, `OAI.InvariantIsing.canonicalFieldLabel`, `OAI.InvariantIsing.cascadeSeedLeaf`, `OAI.InvariantIsing.cascadeSeedPath`, `OAI.InvariantIsing.cavityAffineBaseEquiv`, `OAI.InvariantIsing.cavityAffineCount`, `OAI.InvariantIsing.cavityAffineFullGroup` and 232 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `InvariantIsing_Arrays_MonomialEnumeration`, `InvariantIsing_Arrays_NSpinCascade`, `InvariantIsing_Arrays_NSpinTensorFrozen`, `InvariantIsing_Arrays_PerturbationWeights`, `InvariantIsing_Arrays_TensorContactRegion`, `InvariantIsing_Arrays_TensorDiagonalCGF`, `InvariantIsing_Arrays_TensorProfiles`, `InvariantIsing_Cavity_CavityActualDiagonal`, `InvariantIsing_Cavity_CavityAffineCounts`, `InvariantIsing_Cavity_CavityAffineFamily`, `InvariantIsing_Cavity_CavityAffineRetained`, `InvariantIsing_Cavity_CavityBaseAmplitude`, `InvariantIsing_Cavity_CavityBaseGroups`, `InvariantIsing_Cavity_CavityBaseHaarFactorization`, `InvariantIsing_Cavity_CavityBaseOverlap`, `InvariantIsing_Cavity_CavityBaseReplacement`, `InvariantIsing_Cavity_CavityBlockFactor`, `InvariantIsing_Cavity_CavityBoundaryCutoff`, `InvariantIsing_Cavity_CavityBoundedReweighting`, `InvariantIsing_Cavity_CavityCanonicalBlockLimit`, `InvariantIsing_Cavity_CavityCanonicalGroupAverage`, `InvariantIsing_Cavity_CavityCanonicalLabels`, `InvariantIsing_Cavity_CavityCascadeSpectralLimit`, `InvariantIsing_Cavity_CavityComparisonRates`, `InvariantIsing_Cavity_CavityComplement`, `InvariantIsing_Cavity_CavityCompressionBlocks`, `InvariantIsing_Cavity_CavityCompressionLimitGeometry`, `InvariantIsing_Cavity_CavityConcreteComplement`, `InvariantIsing_Cavity_CavityConcreteFrameOrbit`, `InvariantIsing_Cavity_CavityConditionedFrame`, `InvariantIsing_Cavity_CavityContinuousCutoff`, `InvariantIsing_Cavity_CavityCouplingAlgebra`, `InvariantIsing_Cavity_CavityFactorBound`, `InvariantIsing_Cavity_CavityFiniteCovariance`, `InvariantIsing_Cavity_CavityFiniteDeficitPath`, `InvariantIsing_Cavity_CavityFiniteGroupSelection`, `InvariantIsing_Cavity_CavityFiniteNormalizer`, `InvariantIsing_Cavity_CavityFrameAlgebra`, `InvariantIsing_Cavity_CavityFrameOrbit`, `InvariantIsing_Cavity_CavityFullTilt`, `InvariantIsing_Cavity_CavityGaussianCoordinateMap`, `InvariantIsing_Cavity_CavityGaussianCurveMean`, `InvariantIsing_Cavity_CavityGaussianFactor`, `InvariantIsing_Cavity_CavityGaussianFactorAlgebra`, `InvariantIsing_Cavity_CavityGaussianMarkedLaw`, `InvariantIsing_Cavity_CavityGaussianNodeCovariance`, `InvariantIsing_Cavity_CavityGaussianNodeLaw`, `InvariantIsing_Cavity_CavityGaussianProjection`, `InvariantIsing_Cavity_CavityGaussianRadialMoments`, `InvariantIsing_Cavity_CavityGaussianRankGram`, `InvariantIsing_Cavity_CavityGaussianRotation`, `InvariantIsing_Cavity_CavityGaussianRotationCurve`, `InvariantIsing_Cavity_CavityGaussianRows`, `InvariantIsing_Cavity_CavityGram`, `InvariantIsing_Cavity_CavityGramProbability`, `InvariantIsing_Cavity_CavityGroupBlockGaussian`, `InvariantIsing_Cavity_CavityGroupCovariance`, `InvariantIsing_Cavity_CavityGroupCovariancePositive`, `InvariantIsing_Cavity_CavityGroupGaussian`, `InvariantIsing_Cavity_CavityGroupHaarProjection`, `InvariantIsing_Cavity_CavityGroupProjection`, `InvariantIsing_Cavity_CavityGroupProjectionUniform`, `InvariantIsing_Cavity_CavityGroupedCoordinates`, `InvariantIsing_Cavity_CavityGroupedGram`, `InvariantIsing_Cavity_CavityHaarCascadeMatch`, `InvariantIsing_Cavity_CavityHaarMarkedLaw`, `InvariantIsing_Cavity_CavityHaarSpectralLabels`, `InvariantIsing_Cavity_CavityInnovationLeaves`, `InvariantIsing_Cavity_CavityInnovationPrefix`, `InvariantIsing_Cavity_CavityInnovationTree`, `InvariantIsing_Cavity_CavityLabeledModel`, `InvariantIsing_Cavity_CavityLinearEnvelope`, `InvariantIsing_Cavity_CavityLinearGaussianMoment`, `InvariantIsing_Cavity_CavityLinearIntegrability`, `InvariantIsing_Cavity_CavityLinearSpinEvaluation`, `InvariantIsing_Cavity_CavityLogDetPotential`, `InvariantIsing_Cavity_CavityMarkedTopology`, `InvariantIsing_Cavity_CavityMatrixResolventBound`, `InvariantIsing_Cavity_CavityMeasurableComplement`, `InvariantIsing_Cavity_CavityOrderedBase`, `InvariantIsing_Cavity_CavityOrderedGroups`, `InvariantIsing_Cavity_CavityOrientation`, `InvariantIsing_Cavity_CavityOverlapError`, `InvariantIsing_Cavity_CavityOverlapWeightedTest`, `InvariantIsing_Cavity_CavityPhysicalBase`, `InvariantIsing_Cavity_CavityPhysicalFactor`, `InvariantIsing_Cavity_CavityPhysicalFrameOrbit`, `InvariantIsing_Cavity_CavityPhysicalProjection`, `InvariantIsing_Cavity_CavityPrecisionTiltMoments`, `InvariantIsing_Cavity_CavityPrefixAffineFamily`, `InvariantIsing_Cavity_CavityProjectedForest`, `InvariantIsing_Cavity_CavityProjectedSpinNumerator`, `InvariantIsing_Cavity_CavityProjectionGeometry`, `InvariantIsing_Cavity_CavityProjectionLimit`, `InvariantIsing_Cavity_CavityProjectorCoordinates`, `InvariantIsing_Cavity_CavityQuadraticAlgebra`, `InvariantIsing_Cavity_CavityQuadraticNormalizer`, `InvariantIsing_Cavity_CavityQuadraticStepWeight`, `InvariantIsing_Cavity_CavityQuadraticTree`, `InvariantIsing_Cavity_CavityRDerivative`, `InvariantIsing_Cavity_CavityRationalBaseCounts`, `InvariantIsing_Cavity_CavityRationalCounts`, `InvariantIsing_Cavity_CavityRationalRetained`, `InvariantIsing_Cavity_CavityRationalWindows`, `InvariantIsing_Cavity_CavityRegularizedReweighting`, `InvariantIsing_Cavity_CavityReplicaCutoff`, `InvariantIsing_Cavity_CavityReplicaGaussianAverage`, `InvariantIsing_Cavity_CavityReplicaRadius`, `InvariantIsing_Cavity_CavityReplicaSecant`, `InvariantIsing_Cavity_CavityReservoirFrame`, `InvariantIsing_Cavity_CavityReservoirRotation`, `InvariantIsing_Cavity_CavityResidualFinite`, `InvariantIsing_Cavity_CavityResidualInnovation`, `InvariantIsing_Cavity_CavityResidualPartition`, `InvariantIsing_Cavity_CavityResidueFamily`, `InvariantIsing_Cavity_CavityResolvent`, `InvariantIsing_Cavity_CavityRetainedFrame`, `InvariantIsing_Cavity_CavityRetainedStack`, `InvariantIsing_Cavity_CavityRootedResidual`, `InvariantIsing_Cavity_CavityRootedSpinChange`, `InvariantIsing_Cavity_CavitySampledBlocks`, `InvariantIsing_Cavity_CavityScalarResolventBound`, `InvariantIsing_Cavity_CavitySchurDerivative`, `InvariantIsing_Cavity_CavitySelectedGroupFrames`, `InvariantIsing_Cavity_CavitySelectedReplicaTest`, `InvariantIsing_Cavity_CavitySoftCutoff`, `InvariantIsing_Cavity_CavitySpecialBlocks`, `InvariantIsing_Cavity_CavitySpectralImages`, `InvariantIsing_Cavity_CavitySpectralStabilizer`, `InvariantIsing_Cavity_CavitySpectralStack`, `InvariantIsing_Cavity_CavitySpinIsometry`, `InvariantIsing_Cavity_CavityStrictLevels`, `InvariantIsing_Cavity_CavityStrictUniformPath`, `InvariantIsing_Cavity_CavityUniformMomentConstants`, `InvariantIsing_Cavity_CavityWeakRadialCutoff`, `InvariantIsing_Cavity_CavityWindowGram`, `InvariantIsing_Cavity_CavityWindowInputs`, `InvariantIsing_Cavity_ConsecutiveFieldPressure`, `InvariantIsing_Core_FiniteFieldLabels`, `InvariantIsing_Core_FiniteSpinEntropy`, `InvariantIsing_Core_Model`, `InvariantIsing_Core_UnitBilinearNorm`, `InvariantIsing_Core_Variational`, `InvariantIsing_Core_Ward`, `InvariantIsing_Fields_CascadeSeedLeaf`, `InvariantIsing_Fields_CascadeSeedPath`, `InvariantIsing_Fields_Field`, `InvariantIsing_Fields_FieldCommonDepthLaw`, `InvariantIsing_Fields_FieldMajorantFold`, `InvariantIsing_Fields_FieldParameterGrowth`, `InvariantIsing_Fields_FieldPublishedEvaluation`, `InvariantIsing_Fields_FieldPublishedPairInput`, `InvariantIsing_Fields_FieldScalarLogCoshSecond`, `InvariantIsing_Fields_FieldScalarSecondDerivative`, `InvariantIsing_Fields_FieldSpinFolding`, `InvariantIsing_Fields_FieldSpinSampling`, `InvariantIsing_Fields_FieldVectorSampling`, `InvariantIsing_Fields_LabeledScaledAncestry`, `InvariantIsing_Fields_PriorFrozenReference`, `InvariantIsing_Fields_VectorGaussianTransition`, `InvariantIsing_Fields_VectorTerminalLabeled`, `InvariantIsing_Gaussian_GaussianGramEmpiricalTransform`, `InvariantIsing_Gaussian_GaussianMeanInterpolation`, `InvariantIsing_Haar_HaarDifferentiableCurve`, `InvariantIsing_Haar_HaarPolynomialCurve`, `InvariantIsing_Haar_HaarPolynomialDerivation`, `InvariantIsing_Haar_HaarPolynomialHeat`, `InvariantIsing_Haar_HaarPolynomialLaplacian`, `InvariantIsing_Haar_HaarPolynomialSpace`, `InvariantIsing_Haar_MatrixRotation`, `InvariantIsing_Haar_PlaneRotation`, `InvariantIsing_Haar_PublishedInputs`, `InvariantIsing_Haar_ReflectionSegment`, `InvariantIsing_Haar_SpecialPlaneRotation`, `InvariantIsing_Magnetic_MagneticContinuationJet`, `InvariantIsing_Magnetic_MagneticContinuationRegular`, `InvariantIsing_Magnetic_MagneticContinuationTwoJet`, `InvariantIsing_Magnetic_MagneticFourJet`, `InvariantIsing_Magnetic_MagneticJetProduct`, `InvariantIsing_Magnetic_MagneticScalarFourth`, `InvariantIsing_Magnetic_MagneticScalarThird`, `InvariantIsing_Magnetic_MagneticSpatialFourth`, `InvariantIsing_Magnetic_MagneticSpatialThird`, `InvariantIsing_Magnetic_MagneticUniformSlabBounds`, `InvariantIsing_Magnetic_RestrictedSpinLog`, `InvariantIsing_Pressure_ThermalPressure`, `InvariantIsing_Spectral_Spectral`, `InvariantIsing_Spectral_SpectralArrayGG`, `InvariantIsing_Spectral_SpectralArrayGeometry`, `InvariantIsing_Spectral_SpectralCalculus`, `InvariantIsing_Spectral_SpectralContinuity`, `InvariantIsing_Spectral_SpectralConvexity`, `InvariantIsing_Spectral_SpectralDensityContinuity`, `InvariantIsing_Spectral_SpectralDiagonalPerturbation`, `InvariantIsing_Spectral_SpectralEndpoints`, `InvariantIsing_Spectral_SpectralEnergy`, `InvariantIsing_Spectral_SpectralExistence`, `InvariantIsing_Spectral_SpectralOverlapPaths`, `InvariantIsing_Spectral_SpectralPartition`, `InvariantIsing_Spectral_SpectralPaths`, `InvariantIsing_Spectral_SpectralReplicaLaw`, `IsingPerceptron_CascadePair`, `IsingPerceptron_CountableMonomialGG`, `IsingPerceptron_EnergyShift`, `IsingPerceptron_FieldChain`, `IsingPerceptron_GaussianIntegration`, `IsingPerceptron_JointGGClosure`, `IsingPerceptron_MonomialGgAtMinimum`, `IsingPerceptron_NamespaceSplit`, `IsingPerceptron_ReplicaEnergyCovarianceBound`, `IsingPerceptron_TiltedLabelLaw`, `IsingPerceptron_VariationalDefs`.
--
--   **Imports.** It imports the published bundles `Def_InvariantIsing` and `Def_IsingFiniteness`; the bundle `OAIQ4Ip000` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ258003` and `OAIQ258004`; the statements `OAI.InvariantIsing.cavityFiniteLevel_monotone`, `OAI.InvariantIsing.cavity_quadratic_regular_ae`, `OAI.InvariantIsing.cavity_quadratic_root_tree_law`, `OAI.InvariantIsing.cavity_residual_innovation_leaf_law`, `OAI.InvariantIsing.cavity_residual_partition_log_integral`, `OAI.InvariantIsing.cavity_residual_partition_pos_finite`, `OAI.InvariantIsing.cavity_rooted_quadratic_gaussian`, `OAI.InvariantIsing.cavity_spectral_haar_test_tendsto`, `OAI.InvariantIsing.continuous_cavityCanonicalLabel`, `OAI.InvariantIsing.continuous_cavitySynchronizedBlock`, `OAI.InvariantIsing.finiteMagneticFunctional_real_profile`, `OAI.InvariantIsing.finiteMagneticFunctional_transport_le`, `OAI.InvariantIsing.finiteMagneticVariational_ne_top_bot`, `OAI.InvariantIsing.finiteVariational_ne_top_bot` and `OAI.InvariantIsing.gaussianLipschitzVariance_proved`; the proofs of `OAI.InvariantIsing.cavityFiniteLevel_monotone`, `OAI.InvariantIsing.cavity_cascade_spin_block_tendsto`, `OAI.InvariantIsing.cavity_quadratic_regular_ae`, `OAI.InvariantIsing.cavity_quadratic_root_tree_law`, `OAI.InvariantIsing.cavity_residual_innovation_leaf_law`, `OAI.InvariantIsing.cavity_residual_partition_log_integral`, `OAI.InvariantIsing.cavity_residual_partition_pos_finite`, `OAI.InvariantIsing.continuous_cavityCanonicalLabel`, `OAI.InvariantIsing.continuous_cavitySynchronizedBlock`, `OAI.InvariantIsing.finiteMagneticFunctional_real_profile`, `OAI.InvariantIsing.gaussianLipschitzVariance_proved`, `OAI.InvariantIsing.gaussianPattern_spectralExcess_tendsto`, `OAI.IsingPerceptron.cascadeCompact_spin`, `OAI.IsingPerceptron.enrichedCoordinatePressure_eq_noise` and `OAI.IsingPerceptron.enrichedMeanPressure_field_insert`.
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
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecificLimits.Basic
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
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
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
import Definitions.Def_OAIQ4Ip000

section
-- module Solutions.OAIQ258_II.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_GaussianIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian Integration. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

section FiniteGibbs
variable {S : Type*} [Fintype S]

lemma finitePartition_pos {w : S → ℝ} (hw : GibbsReference w) (H : S → ℝ) :
    0 < finitePartition w H := by
  obtain ⟨x, hx⟩ := hw.2
  exact Finset.sum_pos' (fun y _ => mul_nonneg (hw.1 y) (Real.exp_pos _).le)
    ⟨x, Finset.mem_univ _, mul_pos hx (Real.exp_pos _)⟩

end FiniteGibbs

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_CountableMonomialGG
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable Monomial G G. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma cylinderField_finset_sum {ι : Type*} (s : Finset ι) (a : ι → ℕ →₀ ℝ)
    (g : ℕ → ℝ) : cylinderField (∑ i ∈ s, a i) g = ∑ i ∈ s, cylinderField (a i) g := by
  let L : (ℕ →₀ ℝ) →+ ℝ :=
    { toFun := fun a => cylinderField a g
      map_zero' := by simp [cylinderField]
      map_add' := fun a b => by
        exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul ..) }
  exact map_sum L _ _

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ReplicaEnergyCovarianceBound
attribute [-instance] _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledSpinReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replica Energy Covariance Bound. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma labeledCommonDepth_le (n : ℕ) (v w : LabeledLeaf n) : labeledCommonDepth n v w ≤ n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    dsimp only [labeledCommonDepth]
    split_ifs
    · exact Nat.succ_le_succ (ih _ _)
    · exact Nat.zero_le _

end IsingPerceptron

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

lemma measurable_cascadeRecursion (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {u : ℕ → S × A → S} {F : S → ℝ}
    (hu : ∀ i, Measurable (u i)) (hF : Measurable F) :
    Measurable (cascadeRecursion n b μ u F) := by
  induction n generalizing b μ u with
  | zero => exact hF
  | succ n ih =>
    have hm : Measurable (fun p : S × A => Real.exp (b 0 *
        cascadeRecursion n (fun j => b (j+1)) (fun j => μ (j+1))
          (fun j => u (j+1)) F (u 0 p))) :=
      (measurable_const.mul ((ih _ _ (fun j => hu (j+1))).comp (hu 0))).exp
    exact hm.stronglyMeasurable.integral_prod_right.measurable.log.div_const _

end IsingPerceptron

namespace IsingPerceptron

lemma abs_log_cosh_le (x : ℝ) : |Real.log (Real.cosh x)| ≤ |x| := by
  have hp := Real.cosh_pos x
  rw [abs_of_nonneg (Real.log_nonneg (Real.one_le_cosh x))]
  calc
    _ ≤ Real.log (Real.exp |x|) := by
      apply Real.log_le_log hp
      rw [Real.cosh_eq]
      have h₁ := Real.exp_le_exp.mpr (le_abs_self x)
      have h₂ := Real.exp_le_exp.mpr (neg_le_abs x)
      linarith
    _ = |x| := Real.log_exp _

lemma logCosh_linearGrowth : HasLinearGrowth (fun x : ℝ => Real.log (Real.cosh x)) := by
  refine ⟨0, 1, le_rfl, zero_le_one, fun x => ?_⟩
  simpa only [zero_add, one_mul, Real.norm_eq_abs] using abs_log_cosh_le x

lemma measurable_logCosh : Measurable (fun x : ℝ => Real.log (Real.cosh x)) :=
  Real.measurable_log.comp Real.continuous_cosh.measurable

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_EnergyShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Energy Shift. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron


lemma cylinderField_feature {J : Type*} [Fintype J] (t : J → ℕ) (a : J → ℝ) (g : ℕ → ℝ) :
    cylinderField (featureCoefficients t a) g = ∑ j, a j*g (t j) := by
  classical
  rw [featureCoefficients,cylinderField_finset_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact Finsupp.sum_single_index (by simp)

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_NamespaceSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Namespace Split. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace IsingPerceptron

lemma gibbsProbability_eq_tilted {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν) :
    gibbsProbability ν H = ν.tilted H := by
  exact ite_eq_right (ne_of_gt (_root_.MeasureTheory.integral_exp_pos he))

end IsingPerceptron

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def perturbationAmplitude (N j : ℕ) : ℝ :=
  Real.sqrt N*perturbationScale N*perturbationWeight j

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_TiltedLabelLaw
attribute [-instance] _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tilted Label Law. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron
variable {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

omit [MeasurableSingletonClass I] in
lemma measurable_labeledSpinReference_general (n : ℕ) (ν : Measure I)
    [IsProbabilityMeasure ν] : Measurable (labeledSpinReference n ν) := by
  let κ : Kernel (LabeledTree n) (LabeledLeaf n) :=
    ⟨labeledLeafLaw n,measurable_labeledLeafLaw n⟩
  have : IsMarkovKernel κ := ⟨fun T => by
    change IsProbabilityMeasure (labeledLeafLaw n T)
    infer_instance⟩
  have he : (fun T => ((Kernel.const (LabeledTree n) ν).prod κ) T) =
      labeledSpinReference n ν := by
    funext T
    rw [Kernel.prod_apply,Kernel.const_apply]
    rfl
  rw [← he]
  exact ((Kernel.const (LabeledTree n) ν).prod κ).measurable

end IsingPerceptron

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_JointGGClosure
attribute [-instance] _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
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
namespace IsingPerceptron

lemma treeOverlap_mem (n : ℕ) (x y : LabeledLeaf n) : treeOverlap n x y ∈ Icc (0:ℝ) 1 := by
  constructor
  · unfold treeOverlap; positivity
  · unfold treeOverlap
    apply (div_le_one (by positivity : (0:ℝ) < (n+1:ℕ))).mpr
    exact_mod_cast (labeledCommonDepth_le n x y).trans (Nat.le_succ n)

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_PerturbationWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform finite perturbation sums for the manuscript's geometric weights. -/

noncomputable section

open IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def tensorPerturbationAmplitude (N : ℕ) (u : Fin N → ℝ) (j : Fin N) : ℝ :=
  perturbationAmplitude N j * u j

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_MonomialEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete complete enumeration of the spectral/tree monomials with linear degree cap. -/

noncomputable section

open scoped BigOperators

namespace InvariantIsing

def multidegreeDecode : (m : ℕ) → ℕ → Fin m → ℕ
  | 0, _ => Fin.elim0
  | m + 1, j => Fin.cases (Nat.unpair j).1 (multidegreeDecode m (Nat.unpair j).2)

/-- First `m` coordinates are spectral degrees; the final coordinate is
the tree degree. The constant kernel can be retained harmlessly. -/
def enumeratedSpectralDegree (m j : ℕ) (a : Fin m) : ℕ :=
  multidegreeDecode (m + 1) (j + 1) a.castSucc

def enumeratedTreeDegree (m j : ℕ) : ℕ :=
  multidegreeDecode (m + 1) (j + 1) (Fin.last m)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_Variational
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Spectral overlap deficit

The deficit `D` is equation (1.4) of the manuscript. Global bounded monotone
representatives are used for paths on `(0,1)`; endpoint values never enter the
integrals.
-/

noncomputable section

open MeasureTheory
open scoped Topology

namespace InvariantIsing

lemma pathMeasure_univ : pathMeasure Set.univ = 1 := by
  simp [pathMeasure]

instance instIsProbabilityMeasureRealPathMeasure : IsProbabilityMeasure pathMeasure := ⟨pathMeasure_univ⟩

lemma OverlapPath.measurable (p : OverlapPath) : Measurable p.val :=
  p.monotone.measurable

lemma OverlapPath.integrable_posPart (p : OverlapPath) (r : ℝ) :
    Integrable (fun s => max (p s - r) 0) pathMeasure := by
  apply (integrable_const (max (1 - r) 0)).mono'
    ((p.measurable.sub measurable_const).max measurable_const).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun s => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le_max (sub_le_sub_right (p.le_one s) r) le_rfl

@[simp] lemma deficit_one (p : OverlapPath) : deficit p 1 = 0 := by
  have he : (fun s => max (p s - 1) 0) = (fun _ => (0 : ℝ)) := by
    funext s
    exact max_eq_right (sub_nonpos.mpr (p.le_one s))
  simp [deficit, he]

lemma deficit_nonneg (p : OverlapPath) {r : ℝ} (hr : r ≤ 1) :
    0 ≤ deficit p r := by
  have h : (∫ s, max (p s - r) 0 ∂pathMeasure) ≤ 1 - r := by
    calc
      _ ≤ ∫ _, (1 - r) ∂pathMeasure := by
        apply integral_mono (p.integrable_posPart r) (integrable_const _)
        intro s
        exact max_le (sub_le_sub_right (p.le_one s) r) (sub_nonneg.mpr hr)
      _ = 1 - r := by simp
  unfold deficit
  linarith

lemma deficit_le (p : OverlapPath) (r : ℝ) : deficit p r ≤ 1 - r := by
  have h : 0 ≤ ∫ s, max (p s - r) 0 ∂pathMeasure :=
    integral_nonneg fun _ => le_max_right _ _
  unfold deficit
  linarith

lemma deficit_mem_unit (p : OverlapPath) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    deficit p r ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨deficit_nonneg p hr.2, (deficit_le p r).trans (by linarith [hr.1])⟩

@[simp] lemma deficit_zero (p : OverlapPath) :
    deficit p 0 = 1 - ∫ s, p s ∂pathMeasure := by
  have he : (fun s => max (p s) 0) = p.val := by
    funext s
    exact max_eq_left (p.nonneg s)
  simp only [deficit, sub_zero, he]

lemma complement_max_eq (a r : ℝ) :
    1 - max a r = 1 - r - max (a - r) 0 := by
  rcases le_total a r with h | h
  · rw [max_eq_right h, max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left h, max_eq_left (sub_nonneg.mpr h)]
    ring

lemma OverlapPath.integrable_complement_max (p : OverlapPath) (r : ℝ) :
    Integrable (fun s => 1 - max (p s) r) pathMeasure := by
  simp_rw [complement_max_eq]
  exact (integrable_const (1 - r)).sub (p.integrable_posPart r)

lemma deficit_eq_integral (p : OverlapPath) (r : ℝ) :
    deficit p r = ∫ s, 1 - max (p s) r ∂pathMeasure := by
  simp_rw [complement_max_eq]
  rw [integral_sub (integrable_const _) (p.integrable_posPart r)]
  simp [deficit]

/-- The deficit is 1-Lipschitz in its scalar argument, including at atoms. -/
lemma abs_deficit_sub_le (p : OverlapPath) (r u : ℝ) :
    |deficit p r - deficit p u| ≤ |r - u| := by
  rw [deficit_eq_integral, deficit_eq_integral,
    ← integral_sub (p.integrable_complement_max r) (p.integrable_complement_max u)]
  have h := norm_integral_le_of_norm_le_const (μ := pathMeasure)
    (f := fun s => (1 - max (p s) r) - (1 - max (p s) u))
    (C := |r - u|) (Filter.Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs]
      have he : (1 - max (p s) r) - (1 - max (p s) u) =
          max u (p s) - max r (p s) := by rw [max_comm u, max_comm r]; ring
      rw [he]
      simpa only [abs_sub_comm] using abs_max_sub_max_le_abs u r (p s))
  simpa only [Real.norm_eq_abs, measureReal_def, pathMeasure_univ,
    ENNReal.toReal_one, mul_one] using h

lemma continuous_deficit (p : OverlapPath) : Continuous (deficit p) := by
  have hl : LipschitzWith 1 (deficit p) := by
    apply LipschitzWith.of_dist_le_mul
    intro r u
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using abs_deficit_sub_le p r u
  exact hl.continuous

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_Field
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The one-site Gaussian functional

These are the finite Gaussian recursion and extended-real optimization in
(1.5)--(1.7) of the manuscript. The field supremum stays inside the path
infimum.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

namespace InvariantIsing

/-- The admissible zero covariance field. -/
def zeroField : FieldStep where
  depth := 0
  cut := fun i => i.val
  ordered_cut := by
    intro i j hij
    change (i.val : ℝ) < (j.val : ℝ)
    exact_mod_cast (show i.val < j.val from hij)
  first := by norm_num
  last := by norm_num
  height := fun _ => 0
  nonneg := fun _ => le_rfl
  ordered_height := monotone_const

@[simp] lemma fieldFunction_zero : fieldFunction zeroField = fun _ => 0 := by
  funext s
  simp [fieldFunction, zeroField]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_VariationalDefs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Variational Defs. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron


lemma measurable_gaussianTransform {U : ℝ → ℝ} (hU : Measurable U) (s d : ℝ) :
    Measurable (gaussianTransform s d U) := by
  unfold gaussianTransform
  split
  · exact (hU.comp (measurable_fst.add (measurable_snd.const_mul _))).stronglyMeasurable.integral_prod_right'.measurable
  · exact Real.measurable_log.comp (((hU.comp
      (measurable_fst.add (measurable_snd.const_mul _))).const_mul d).exp.stronglyMeasurable.integral_prod_right'.measurable) |>.div_const d

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_CascadePair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cascade Pair. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma uniformCellIndex_le (n : ℕ) (u : ℝ) : uniformCellIndex n u ≤ n := min_le_left _ _

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma uniformCell_measure (n i : ℕ) :
    (volume.restrict (Ioo ((i:ℝ)/(n+1:ℕ)) (((i:ℝ)+1)/(n+1:ℕ)))).real univ = 1/(n+1:ℕ) := by
  rw [measureReal_def,Measure.restrict_apply_univ,Real.volume_Ioo]
  have he : (((i:ℝ)+1)/(n+1:ℕ))-(i:ℝ)/(n+1:ℕ) = 1/(n+1:ℕ) := by ring
  rw [he,ENNReal.toReal_ofReal (by positivity)]

lemma uniformCell_const (n i : ℕ) (c : ℝ) :
    ((n+1:ℕ):ℝ)*(∫ _ in Ioo ((i:ℝ)/(n+1:ℕ)) (((i:ℝ)+1)/(n+1:ℕ)), c) = c := by
  rw [integral_const,smul_eq_mul,uniformCell_measure]
  field_simp

lemma uniformCell_integrable {q : ℝ → ℝ} (hq : Monotone q)
    (hb : ∀ u, q u ∈ Icc (0:ℝ) 1) (n i : ℕ) :
    IntegrableOn q (Ioo ((i:ℝ)/(n+1:ℕ)) (((i:ℝ)+1)/(n+1:ℕ))) := by
  apply Integrable.of_bound hq.measurable.aestronglyMeasurable 1
  exact ae_of_all _ (fun u => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hb u).1] using (hb u).2)

lemma uniformCellAverage_bounds {q : ℝ → ℝ} (hq : Monotone q)
    (hb : ∀ u, q u ∈ Icc (0:ℝ) 1) (n i : ℕ) :
    q ((i:ℝ)/(n+1:ℕ)) ≤ uniformCellAverage q n i ∧
      uniformCellAverage q n i ≤ q (((i:ℝ)+1)/(n+1:ℕ)) := by
  have hi := uniformCell_integrable hq hb n i
  have hn : (0:ℝ) ≤ (n+1:ℕ) := by positivity
  constructor
  · rw [← uniformCell_const n i (q ((i:ℝ)/(n+1:ℕ)))]
    apply mul_le_mul_of_nonneg_left _ hn
    apply integral_mono_ae (integrable_const _) hi
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact hq hu.1.le
  · rw [← uniformCell_const n i (q (((i:ℝ)+1)/(n+1:ℕ)))]
    apply mul_le_mul_of_nonneg_left _ hn
    apply integral_mono_ae hi (integrable_const _)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact hq hu.2.le

lemma uniformCellAverage_mem {q : ℝ → ℝ} (hq : Monotone q)
    (hb : ∀ u, q u ∈ Icc (0:ℝ) 1) (n i : ℕ) : uniformCellAverage q n i ∈ Icc (0:ℝ) 1 :=
  ⟨(hb _).1.trans (uniformCellAverage_bounds hq hb n i).1,
    (uniformCellAverage_bounds hq hb n i).2.trans (hb _).2⟩

lemma uniformCellAverage_monotone {q : ℝ → ℝ} (hq : Monotone q)
    (hb : ∀ u, q u ∈ Icc (0:ℝ) 1) (n : ℕ) : Monotone (uniformCellAverage q n) := by
  intro i j hij
  rcases eq_or_lt_of_le hij with rfl|hij
  · rfl
  · apply (uniformCellAverage_bounds hq hb n i).2.trans
    apply le_trans _ (uniformCellAverage_bounds hq hb n j).1
    apply hq
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.succ_le_of_lt hij

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix InnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_FieldChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Field Chain. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma chainExponent_apply {n : ℕ} (ζ : Fin (n+2) → ℝ) {i : ℕ} (hi : i<n) :
    chainExponent ζ i = ζ ⟨i+1,by omega⟩ := by simp [chainExponent,min_eq_left (by omega : i+1 ≤ n+1)]

lemma chainExponent_admissible {n : ℕ} {ζ : Fin (n+2) → ℝ} (hz : StrictMono ζ)
    (hfirst : ζ 0=0) (hlast : ζ (Fin.last (n+1))=1) : CascadeExponents n (chainExponent ζ) := by
  constructor
  · intro i hi
    rw [chainExponent_apply ζ hi]
    constructor
    · rw [← hfirst]
      exact hz (by change (0 : ℕ) < i+1; omega)
    · rw [← hlast]
      exact hz (by change i+1 < n+1; omega)
  · intro i j hij hj
    rw [chainExponent_apply ζ (by omega),chainExponent_apply ζ hj]
    exact hz (by simpa using (show i+1<j+1 by omega))

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open scoped BigOperators





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

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

lemma sum_exp_pos {X : Type*} [Fintype X] [Nonempty X] (H : X → ℝ) :
    0 < ∑ x, Real.exp (H x) := by
  exact Finset.sum_pos (fun x _ => Real.exp_pos (H x)) Finset.univ_nonempty

end InvariantIsing

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

def vectorGaussianLaw (N : ℕ) (v : ℝ≥0) : ProbabilityMeasure (Fin N → ℝ) :=
  ⟨Measure.pi (fun _ : Fin N => gaussianReal 0 v), (by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_PublishedInputs
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Haar concentration and Gaussian Poincaré inequalities.

Gromov–Milman, *A topological application of the isoperimetric inequality*,
American Journal of Mathematics 105 (1983), 843–854, Section 1.2,
Remark 2, and the special-orthogonal example in Section 3.4 give the
following concentration specialization.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators NNReal

namespace InvariantIsing

abbrev SpecialOrthogonal (N : ℕ) := Matrix.specialOrthogonalGroup (Fin N) ℝ

/-- Frobenius distance, with the unnormalized matrix-coordinate convention. -/
def frobeniusDistance {N : ℕ} (U V : SpecialOrthogonal N) : ℝ :=
  Real.sqrt (∑ i, ∑ j, ((U : Matrix (Fin N) (Fin N) ℝ) i j -
    (V : Matrix (Fin N) (Fin N) ℝ) i j) ^ 2)

/-- The finite-dimensional Gaussian Poincaré inequality specialized to a
globally Lipschitz function. The Euclidean norm is essential: a coordinatewise
bound for the supremum norm would introduce a dimension factor.

Published source: Bakry–Émery, *Diffusions hypercontractives*, Séminaire de
Probabilités XIX (1985), Proposition 5, equation (20), p.198, with `U(x)=x²`,
and Corollary 2, equation (23), p.199, with the Ornstein–Uhlenbeck example
on pp.199–200 (the carré-du-champ calculation is on p.186). The usual
Lipschitz specialization follows by smooth approximation. -/
def GaussianLipschitzVarianceInput : Prop :=
  ∀ d : ℕ, ∀ L : ℝ≥0, ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
    LipschitzWith L f →
      ProbabilityTheory.variance f (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
        (L : ℝ) ^ 2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_MatrixRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relating the orthogonal matrix and Euclidean-isometry models. -/

noncomputable section

open scoped BigOperators Matrix

namespace InvariantIsing

@[simp] lemma matrixRotation_apply {N : ℕ} (U : Orthogonal N)
    (v : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    matrixRotation U v i = ∑ j, (U : Matrix (Fin N) (Fin N) ℝ) i j * v j := rfl

/-- Restricting from O(N) to SO(N) preserves the same spectral action. -/
def specialRotation {N : ℕ} (U : SpecialOrthogonal N) : Rotation N :=
  matrixRotation ⟨U.val, (Matrix.mem_specialOrthogonalGroup_iff.mp U.property).1⟩

@[simp] lemma specialRotation_apply {N : ℕ} (U : SpecialOrthogonal N)
    (v : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    specialRotation U v i = ∑ j, (U : Matrix (Fin N) (Fin N) ℝ) i j * v j := rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript's linear enrichment and monomial tree variance increments. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

def varianceIncrement (q : ℕ → ℝ) (i : ℕ) : ℝ≥0 := (pathIncrement q i).toNNReal

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorFrozen
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

abbrev TensorFrozenData (N n : ℕ) (j : ℕ) := (SpecialOrthogonal N × LabeledTree n) × OtherNamespaces (j + 1)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianMeanInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Gaussian mean interpolation with arbitrary base energy and weights. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {X : Type*} [Fintype X]

def affineGaussianCoefficients {d : ℕ} (C A : X → Fin d → ℝ) (s : ℝ) : X → Fin d → ℝ :=
  fun x i => C x i + s * A x i

def affineGaussianMean {d : ℕ} (w H : X → ℝ) (C A : X → Fin d → ℝ) (s : ℝ) : ℝ :=
  ∫ g, Real.log (finitePartition w (fun x => H x +
    linearGaussian (affineGaussianCoefficients C A s) g x))
      ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1)

def affineGaussianSlope {d : ℕ} (w H : X → ℝ) (C A : X → Fin d → ℝ) (s : ℝ) : ℝ :=
  ∫ g, ∑ x, gaussianGibbs w H (affineGaussianCoefficients C A s) g x * linearGaussian A g x
    ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralDiagonalPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The deterministic spectral-diagonal perturbation as an exact eigenvalue shift. -/

noncomputable section

open IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def diagonalPerturbedEigenvalues {N m : ℕ} (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (v : Fin m → ℝ) (t : ℝ) (i : Fin N) : ℝ :=
  t * eig i + 2 * perturbationScale N * ∑ a, if i ∈ I a then v a else 0

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorDiagonalCGF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual spectral-diagonal coordinate as a bounded frozen tilt. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

abbrev TensorFlatDisorder (N n : ℕ) := (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ)

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

abbrev TensorContactParameter (N m n : ℕ) :=
  ℝ × (Fin (n + 1) → ℝ) × (Fin N → ℝ) × (Fin m → ℝ)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityActualDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The deterministic perturbation error under a fixed cavity-size
jump, stated for the actual spectral-diagonal perturbation energy. -/

noncomputable section
open IsingPerceptron Filter
open scoped BigOperators Topology

namespace InvariantIsing

def cavityDeterministicRate (n m : ℕ) (C : ℝ) (N : ℕ) : ℝ :=
  2 * m * (|(N + n) * perturbationScale (N + n) - N * perturbationScale N| +
    C * perturbationScale N)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBoundedReweighting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded positive reweighting of random probability priors.  Its
replica-test limit follows from the unreweighted extra-replica limits. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

def cavityWeightNormalizer {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (w : X → ℝ) : ℝ := ∫ x, w x ∂ν

def cavityWeightNumerator {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (w : X → ℝ) {r : ℕ} (F : (Fin r → X) → ℝ) : ℝ :=
  ∫ σ : Fin r → X, (∏ i, w (σ i)) * F σ ∂Measure.pi (fun _ => ν)

def cavityWeightedReplicaMean {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (w : X → ℝ) {r : ℕ} (F : (Fin r → X) → ℝ) : ℝ :=
  cavityWeightNumerator ν w F / cavityWeightNormalizer ν w ^ r

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_Ward
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-volume Gibbs rotation identity

Differentiation of a normalized Gibbs average produces the observable
variation and its covariance with the Hamiltonian variation. Haar invariance
then gives their exact integral identity. The spin prior may have zero weights.
No limiting Ward equations or pressure bounds are assumed here.
-/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators Topology

namespace InvariantIsing

variable {S : Type*} [Fintype S]

/-- Finite normalized Gibbs expectation, for an arbitrary nonzero positive prior. -/
def gibbsAverage (w H A : S → ℝ) : ℝ :=
  ∑ σ, finiteGibbs w H σ * A σ

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBlockFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite-volume algebra for the coupled cavity comparison.  The
spectral coupling and its Gaussian limit are separate source obligations. -/

noncomputable section
open IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

def cavityQuadratic {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (y : Fin d → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, y i * A i j * y j

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityResolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The noncommuting resolvent identities in the quadratic cavity tilt.
These finite matrix statements include the zero-dimensional convention. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

def cavityResolvent {d : ℕ} (K B : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (1 - B * K)⁻¹ * B

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityQuadraticAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-dimensional algebra in `cav:q-factor` and the backward
quadratic recursion.  The factors retain their order: neither the two
covariances nor the quadratic coefficient need commute. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

/-- The coefficient `K_i = K (1 - H_i K)⁻¹` of the backward quadratic. -/
def cavityBackwardQuadratic {d : ℕ} (K H : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ := K * (1 - H * K)⁻¹

/-- The conditional-mean matrix at a step from covariance `P` to `C`. -/
def cavityStepTransition {d : ℕ} (K P C : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ := (1 - (P - C) * cavityBackwardQuadratic K C)⁻¹

@[simp] theorem cavityBackwardQuadratic_zero {d : ℕ} (K : Matrix (Fin d) (Fin d) ℝ) :
    cavityBackwardQuadratic K 0 = K := by
  simp [cavityBackwardQuadratic]

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

def cavityGaussianRow (q : ℕ) : Measure (Fin q → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

def cavityGaussianRows (q : ℕ) : Measure (ℕ → Fin q → ℝ) :=
  Measure.infinitePi (fun _ => cavityGaussianRow q)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Eventual nondegeneracy of the Gaussian Gram matrix used to construct
fresh orthonormal directions. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix

namespace InvariantIsing

def cavityEmpiricalGram {q : ℕ} (x : ℕ → Fin q → ℝ) (n : ℕ) :
    Matrix (Fin q) (Fin q) ℝ :=
  fun i j => (∑ k ∈ Finset.range n, x k i * x k j) / (n : ℝ)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGramProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nondegenerate Gaussian frames have probability tending to one.
This also supplies the positive mass needed to condition the finite frame
construction, without any assertion about zero sets of polynomials. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

namespace InvariantIsing

def cavityGoodGram (q n : ℕ) : Set (ℕ → Fin q → ℝ) :=
  {x | 0 < (cavityEmpiricalGram x n).det}

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFrameAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Gaussian frame construction: normalize the column Gram
matrix by its positive square root. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

def cavityGaussianMatrix {q : ℕ} (x : ℕ → Fin q → ℝ) (n : ℕ) :
    Matrix (Fin n) (Fin q) ℝ :=
  fun k i => x k i / Real.sqrt n

def cavityNormalizeFrame {n q : ℕ} (A : Matrix (Fin n) (Fin q) ℝ) :
    Matrix (Fin n) (Fin q) ℝ :=
  A * (CFC.sqrt (A.transpose * A))⁻¹

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFrameOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix form of transitivity and continuity of the frame orbit action. -/

noncomputable section
open MeasureTheory
open scoped Matrix

namespace InvariantIsing

def cavityRotationMatrix {n : ℕ} (U : Rotation n) : Orthogonal n :=
  ⟨U.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis,
    U.toMatrix_mem_unitaryGroup (EuclideanSpace.basisFun (Fin n) ℝ)
      (EuclideanSpace.basisFun (Fin n) ℝ)⟩

lemma continuous_cavityFrameAction (n q : ℕ) :
    Continuous (fun p : Orthogonal n × Matrix (Fin n) (Fin q) ℝ =>
      (p.1 : Matrix (Fin n) (Fin n) ℝ) * p.2) := by
  exact (continuous_subtype_val.comp continuous_fst).matrix_mul continuous_snd

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianRadialMoments
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dimension-explicit Gaussian radial moments used to bound moments of
uniform spherical projections. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

namespace InvariantIsing

def cavityGaussianAbsMoment (p : ℕ) : ℝ :=
  ∫ z : ℝ, |z| ^ p ∂gaussianReal 0 1

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRegularizedReweighting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extra-replica limits for bounded nonnegative factors, with the
normalizer regularized before any cutoff is removed. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

def cavityRegularizedReplicaMean {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (w : X → ℝ) {r : ℕ} (F : (Fin r → X) → ℝ) (δ : ℝ) : ℝ :=
  cavityWeightNumerator ν w F / (cavityWeightNormalizer ν w + δ) ^ r

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFactorBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quadratic growth bound for the actual cavity exponent. The bound
does not require the special-coordinate block matrices to commute. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def cavityMatrixMass {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, |A i j|

lemma cavityMatrixMass_nonneg {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) :
    0 ≤ cavityMatrixMass A := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySoftCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous cutoffs for finite-replica passage. Their removal costs
only the discarded mass, including the zero-normalizer convention. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Topology

namespace InvariantIsing

def cavityRadialCutoff (B x : ℝ) : ℝ := max 0 (min 1 (B + 1 - x))

lemma continuous_cavityRadialCutoff (B : ℝ) : Continuous (cavityRadialCutoff B) := by
  unfold cavityRadialCutoff
  fun_prop

lemma cavityRadialCutoff_mem (B x : ℝ) : cavityRadialCutoff B x ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityContinuousCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded continuous cutoffs of the actual cavity factor. The radius
cutoff equals one on the inner ball and vanishes outside the next ball. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

def cavityFactorSize {d n : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  cavityMatrixMass K + cavityMatrixMass L + cavityMatrixMass C

lemma cavityFactorSize_nonneg {d n : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ cavityFactorSize K L C := add_nonneg
      (add_nonneg (cavityMatrixMass_nonneg K) (cavityMatrixMass_nonneg L)) (cavityMatrixMass_nonneg C)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_Spectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite spectral resolvents

The finite-alphabet arguments in Sections 3 and 5 of the manuscript use
the unique solution of `∑ a, ρ a / (b - eig a) = x` above all eigenvalues.
The solution is unique and satisfies deterministic bounds.
The weights may vanish; their sum being one is the only normalization.
-/

noncomputable section

open scoped BigOperators

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

/-- The Cauchy transform of a finite spectral probability law. -/
def finiteResolvent (ρ eig : ι → ℝ) (b : ℝ) : ℝ :=
  ∑ a, ρ a / (b - eig a)

/-- The second resolvent moment, which controls the derivative of the inverse. -/
def finiteSecondResolvent (ρ eig : ι → ℝ) (b : ℝ) : ℝ :=
  ∑ a, ρ a / (b - eig a) ^ 2

theorem exists_pos_spectral_weight {ρ : ι → ℝ}
    (hρ : ∀ a, 0 ≤ ρ a) (hρsum : ∑ a, ρ a = 1) :
    ∃ a, 0 < ρ a := by
  by_contra h
  push Not at h
  have hz : ∑ a, ρ a = 0 := Finset.sum_eq_zero fun a _ =>
    le_antisymm (h a) (hρ a)
  linarith

theorem finiteResolvent_pos {ρ eig : ι → ℝ} {b : ℝ}
    (hρ : ∀ a, 0 ≤ ρ a) (hρsum : ∑ a, ρ a = 1)
    (hb : ∀ a, eig a < b) :
    0 < finiteResolvent ρ eig b := by
  obtain ⟨a, ha⟩ := exists_pos_spectral_weight hρ hρsum
  unfold finiteResolvent
  exact Finset.sum_pos' (fun a _ => div_nonneg (hρ a) (sub_pos.mpr (hb a)).le)
    ⟨a, Finset.mem_univ a, div_pos ha (sub_pos.mpr (hb a))⟩

theorem finiteResolvent_strictAnti {ρ eig : ι → ℝ} {b c : ℝ}
    (hρ : ∀ a, 0 ≤ ρ a) (hρsum : ∑ a, ρ a = 1)
    (hb : ∀ a, eig a < b) (hbc : b < c) :
    finiteResolvent ρ eig c < finiteResolvent ρ eig b := by
  obtain ⟨a, ha⟩ := exists_pos_spectral_weight hρ hρsum
  apply Finset.sum_lt_sum
  · intro j _
    exact div_le_div_of_nonneg_left (hρ j) (sub_pos.mpr (hb j)) (by linarith)
  · exact ⟨a, Finset.mem_univ a,
      div_lt_div_of_pos_left ha (sub_pos.mpr (hb a)) (by linarith)⟩

/-- The finite-alphabet inverse is unique on its required branch. -/
theorem finiteResolvent_solution_unique {ρ eig : ι → ℝ} {b c x : ℝ}
    (hρ : ∀ a, 0 ≤ ρ a) (hρsum : ∑ a, ρ a = 1)
    (hb : ∀ a, eig a < b) (hc : ∀ a, eig a < c)
    (hbx : finiteResolvent ρ eig b = x) (hcx : finiteResolvent ρ eig c = x) :
    b = c := by
  rcases lt_trichotomy b c with h | h | h
  · have := finiteResolvent_strictAnti hρ hρsum hb h
    linarith
  · exact h
  · have := finiteResolvent_strictAnti hρ hρsum hc h
    linarith

theorem finiteResolvent_le {ρ eig : ι → ℝ} {b u : ℝ}
    (hρ : ∀ a, 0 ≤ ρ a) (hρsum : ∑ a, ρ a = 1)
    (heig : ∀ a, eig a ≤ u) (hb : u < b) :
    finiteResolvent ρ eig b ≤ 1 / (b - u) := by
  calc
    finiteResolvent ρ eig b ≤ ∑ a, ρ a / (b - u) := by
      apply Finset.sum_le_sum
      intro a _
      exact div_le_div_of_nonneg_left (hρ a) (sub_pos.mpr hb) (by linarith [heig a])
    _ = 1 / (b - u) := by rw [← Finset.sum_div, hρsum]

theorem le_finiteResolvent {ρ eig : ι → ℝ} {b l : ℝ}
    (hρ : ∀ a, 0 ≤ ρ a) (hρsum : ∑ a, ρ a = 1)
    (heig : ∀ a, l ≤ eig a) (hb : ∀ a, eig a < b) :
    1 / (b - l) ≤ finiteResolvent ρ eig b := by
  calc
    1 / (b - l) = ∑ a, ρ a / (b - l) := by rw [← Finset.sum_div, hρsum]
    _ ≤ finiteResolvent ρ eig b := by
      apply Finset.sum_le_sum
      intro a _
      exact div_le_div_of_nonneg_left (hρ a) (sub_pos.mpr (hb a)) (by linarith [heig a])

/-- Section 6's bound for the uncapped inverse transform. -/
theorem finiteR_bounds {ρ eig : ι → ℝ} {b x l u : ℝ}
    (hρ : ∀ a, 0 ≤ ρ a) (hρsum : ∑ a, ρ a = 1)
    (hl : ∀ a, l ≤ eig a) (hu : ∀ a, eig a ≤ u)
    (hb : u < b) (hx : 0 < x) (hbx : finiteResolvent ρ eig b = x) :
    l ≤ b - 1 / x ∧ b - 1 / x ≤ u := by
  have hbeig : ∀ a, eig a < b := fun a => lt_of_le_of_lt (hu a) hb
  have hupper := finiteResolvent_le hρ hρsum hu hb
  have hlower := le_finiteResolvent hρ hρsum hl hbeig
  rw [hbx] at hupper hlower
  obtain ⟨a, _⟩ := exists_pos_spectral_weight hρ hρsum
  have hbl : 0 < b - l := by linarith [hl a, hbeig a]
  have hbu : 0 < b - u := sub_pos.mpr hb
  have hbux : (b - u) * x ≤ 1 := by
    simpa only [mul_comm] using (le_div_iff₀ hbu).mp hupper
  have hblx : 1 ≤ (b - l) * x := by
    simpa only [mul_comm] using (div_le_iff₀ hbl).mp hlower
  constructor
  · have : 1 / x ≤ b - l := (div_le_iff₀ hx).mpr hblx
    linarith
  · have : b - u ≤ 1 / x := (le_div_iff₀ hx).mpr hbux
    linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The inverse Cauchy transform of a finite alphabet always lies strictly
above its largest atom. This supplies existence, as well as uniqueness,
for the resolvent used by the finite-alphabet cavity construction.
-/

noncomputable section

open scoped BigOperators
open Set

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem continuousOn_finiteResolvent (ρ eig : ι → ℝ) (s : Set ℝ)
    (hs : ∀ b ∈ s, ∀ a, eig a < b) :
    ContinuousOn (finiteResolvent ρ eig) s := by
  unfold finiteResolvent
  apply continuousOn_finsetSum
  intro a _
  exact continuousOn_const.div (continuousOn_id.sub continuousOn_const)
    (fun b hb => ne_of_gt (sub_pos.mpr (hs b hb a)))

/-- Existence and uniqueness above an upper edge carrying positive mass. -/
theorem exists_unique_finiteResolvent_solution {ρ eig : ι → ℝ} {a₀ : ι} {x : ℝ}
    (hρ : ∀ a, 0 ≤ ρ a) (hρsum : ∑ a, ρ a = 1)
    (ha₀ : 0 < ρ a₀) (he : ∀ a, eig a ≤ eig a₀) (hx : 0 < x) :
    ∃! b : ℝ, (∀ a, eig a < b) ∧ finiteResolvent ρ eig b = x := by
  let lo := eig a₀ + ρ a₀ / (2 * x)
  let hi := lo + 1 / x
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hdist : 0 < ρ a₀ / (2 * x) := div_pos ha₀ (by positivity)
  have helo : eig a₀ < lo := by dsimp [lo] <;> linarith
  have hlohi : lo < hi := by dsimp [hi] <;> linarith [one_div_pos.mpr hx]
  have hEiglo : ∀ a, eig a < lo := fun a => (he a).trans_lt helo
  have hsingle : ρ a₀ / (lo - eig a₀) = 2 * x := by
    dsimp [lo]
    field_simp [ne_of_gt ha₀]
    ring
  have hxlo : x ≤ finiteResolvent ρ eig lo := by
    have hterm : ρ a₀ / (lo - eig a₀) ≤ finiteResolvent ρ eig lo :=
      Finset.single_le_sum (fun a _ => div_nonneg (hρ a) (sub_pos.mpr (hEiglo a)).le)
        (Finset.mem_univ a₀)
    rw [hsingle] at hterm
    linarith
  have hhiedge : eig a₀ < hi := helo.trans hlohi
  have hupper := finiteResolvent_le hρ hρsum he hhiedge
  have hxhi : finiteResolvent ρ eig hi ≤ x := by
    apply hupper.trans
    have hhidist : 1 / x ≤ hi - eig a₀ := by dsimp [hi, lo] <;> linarith
    have h := one_div_le_one_div_of_le (one_div_pos.mpr hx) hhidist
    simpa using h
  have hcont : ContinuousOn (finiteResolvent ρ eig) (Icc lo hi) :=
    continuousOn_finiteResolvent ρ eig _ (fun b hb a => (hEiglo a).trans_le hb.1)
  obtain ⟨b, hb, hbx⟩ := intermediate_value_Icc' hlohi.le hcont ⟨hxhi, hxlo⟩
  have hbEig : ∀ a, eig a < b := fun a => (hEiglo a).trans_le hb.1
  refine ⟨b, ⟨hbEig, hbx⟩, ?_⟩
  intro c hc
  exact finiteResolvent_solution_unique hρ hρsum hc.1 hbEig hc.2 hbx

/-- In particular every finite spectral probability law with positive masses
has an uncapped inverse at every positive argument. -/
theorem exists_unique_finiteResolvent_of_pos {ρ eig : ι → ℝ} {x : ℝ}
    (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (hx : 0 < x) :
    ∃! b : ℝ, (∀ a, eig a < b) ∧ finiteResolvent ρ eig b = x := by
  classical
  obtain ⟨a, _⟩ := exists_pos_spectral_weight (fun a => (hρ a).le) hρsum
  have hnonempty : (Finset.univ : Finset ι).Nonempty := ⟨a, Finset.mem_univ a⟩
  obtain ⟨a₀, _, he⟩ := Finset.exists_max_image Finset.univ eig hnonempty
  exact exists_unique_finiteResolvent_solution (fun a => (hρ a).le) hρsum
    (hρ a₀) (fun a => he a (Finset.mem_univ a)) hx

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

/-- Third resolvent moment. -/
def finiteThirdResolvent (ρ eig : ι → ℝ) (b : ℝ) : ℝ :=
  ∑ a, ρ a / (b - eig a) ^ 3

theorem finiteSecondResolvent_pos {ρ eig : ι → ℝ} {b : ℝ}
    (hρ : ∀ a, 0 ≤ ρ a) (hρsum : ∑ a, ρ a = 1)
    (hb : ∀ a, eig a < b) :
    0 < finiteSecondResolvent ρ eig b := by
  obtain ⟨a, ha⟩ := exists_pos_spectral_weight hρ hρsum
  unfold finiteSecondResolvent
  exact Finset.sum_pos' (fun a _ => div_nonneg (hρ a) (sq_nonneg _))
    ⟨a, Finset.mem_univ a, div_pos ha (sq_pos_of_pos (sub_pos.mpr (hb a)))⟩

theorem hasStrictDerivAt_finiteResolvent (ρ eig : ι → ℝ) {b : ℝ}
    (hb : ∀ a, eig a < b) :
    HasStrictDerivAt (finiteResolvent ρ eig) (-finiteSecondResolvent ρ eig b) b := by
  have hterm : ∀ a, HasStrictDerivAt (fun z : ℝ => ρ a / (z - eig a))
      (-ρ a / (b - eig a) ^ 2) b := by
    intro a
    simpa only [id_eq, zero_mul, mul_one, zero_sub] using
      (hasStrictDerivAt_const b (ρ a)).fun_div
        ((hasStrictDerivAt_id b).sub_const (eig a)) (ne_of_gt (sub_pos.mpr (hb a)))
  convert! HasStrictDerivAt.fun_sum (u := Finset.univ) (fun a _ => hterm a) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [finiteSecondResolvent, neg_div, Finset.sum_neg_distrib]

theorem hasStrictDerivAt_finiteSecondResolvent (ρ eig : ι → ℝ) {b : ℝ}
    (hb : ∀ a, eig a < b) :
    HasStrictDerivAt (finiteSecondResolvent ρ eig) (-2 * finiteThirdResolvent ρ eig b) b := by
  have hterm : ∀ a, HasStrictDerivAt (fun z : ℝ => ρ a / (z - eig a) ^ 2)
      (-2 * (ρ a / (b - eig a) ^ 3)) b := by
    intro a
    have hd : HasStrictDerivAt (fun z : ℝ => z - eig a) 1 b := by
      convert! (hasStrictDerivAt_id b).sub_const (eig a) using 1
      all_goals try with_reducible_and_instances rfl
    convert (hasStrictDerivAt_const b (ρ a)).fun_div
      (hd.fun_pow 2)
      (pow_ne_zero 2 (ne_of_gt (sub_pos.mpr (hb a)))) using 1
    all_goals try with_reducible_and_instances rfl
    field_simp [ne_of_gt (sub_pos.mpr (hb a))]
    ring
  convert! HasStrictDerivAt.fun_sum (u := Finset.univ) (fun a _ => hterm a) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [finiteThirdResolvent, Finset.mul_sum]

/-- Inverse transform for a finite alphabet with positive masses.
The value outside positive arguments is irrelevant to the application. -/
def finiteInverse (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (x : ℝ) : ℝ :=
  if hx : 0 < x then (exists_unique_finiteResolvent_of_pos (eig := eig) hρ hρsum hx).choose else 0

theorem finiteInverse_spec (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 < x) :
    (∀ a, eig a < finiteInverse ρ eig hρ hρsum x) ∧
      finiteResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) = x := by
  simp only [finiteInverse, dite_eq_left hx]
  exact (exists_unique_finiteResolvent_of_pos (eig := eig) hρ hρsum hx).choose_spec.1

theorem finiteInverse_left (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {b : ℝ} (hb : ∀ a, eig a < b) :
    finiteInverse ρ eig hρ hρsum (finiteResolvent ρ eig b) = b := by
  have hx := finiteResolvent_pos (fun a => (hρ a).le) hρsum hb
  have hs := finiteInverse_spec ρ eig hρ hρsum hx
  exact finiteResolvent_solution_unique (fun a => (hρ a).le) hρsum hs.1 hb hs.2 rfl

/-- The exact inverse derivative appearing in the finite-spectrum calculation. -/
theorem hasStrictDerivAt_finiteInverse (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 < x) :
    HasStrictDerivAt (finiteInverse ρ eig hρ hρsum)
      (-1 / finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x)) x := by
  let b := finiteInverse ρ eig hρ hρsum x
  have hs := finiteInverse_spec ρ eig hρ hρsum hx
  have hpos := finiteSecondResolvent_pos (fun a => (hρ a).le) hρsum hs.1
  have hd := hasStrictDerivAt_finiteResolvent ρ eig hs.1
  have hnear : ∀ᶠ z : ℝ in 𝓝 b, ∀ a, eig a < z := by
    apply Filter.eventually_all.mpr
    intro a
    exact Ioi_mem_nhds (hs.1 a)
  have hinv : ∀ᶠ z : ℝ in 𝓝 b,
      finiteInverse ρ eig hρ hρsum (finiteResolvent ρ eig z) = z := by
    filter_upwards [hnear] with z hz
    exact finiteInverse_left ρ eig hρ hρsum hz
  have hi := hd.to_local_left_inverse (neg_ne_zero.mpr hpos.ne') hinv
  rw [hs.2] at hi
  simpa only [inv_neg, one_div, neg_div] using hi

/-- Finite-alphabet `R`-transform, with its prescribed value at zero. -/
def finiteR (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (x : ℝ) : ℝ :=
  if 0 < x then finiteInverse ρ eig hρ hρsum x - 1 / x else ∑ a, ρ a * eig a

theorem hasStrictDerivAt_finiteR (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 < x) :
    HasStrictDerivAt (finiteR ρ eig hρ hρsum)
      (-1 / finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) + 1 / x ^ 2) x := by
  have hb := hasStrictDerivAt_finiteInverse ρ eig hρ hρsum hx
  have hi : HasStrictDerivAt (fun y : ℝ => 1 / y) (-1 / x ^ 2) x := by
    simpa using (hasStrictDerivAt_const x (1 : ℝ)).fun_div
      (hasStrictDerivAt_id x) (ne_of_gt hx)
  have h := hb.fun_sub hi
  have heq : finiteR ρ eig hρ hρsum =ᶠ[𝓝 x]
      fun y => finiteInverse ρ eig hρ hρsum y - 1 / y := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp only [finiteR, ite_eq_left (show 0 < y from hy)]
  convert h.congr_of_eventuallyEq heq.symm using 1
  all_goals try with_reducible_and_instances rfl
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralConvexity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convexity of the spectral energy primitive, including zero. -/

noncomputable section

open scoped BigOperators Topology
open Filter Set

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem finiteR_mem_interval (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {l u : ℝ}
    (hl : ∀ a, l ≤ eig a) (hu : ∀ a, eig a ≤ u) (x : ℝ) :
    l ≤ finiteR ρ eig hρ hρsum x ∧ finiteR ρ eig hρ hρsum x ≤ u := by
  by_cases hx : 0 < x
  · simp only [finiteR, ite_eq_left hx]
    have hs := finiteInverse_spec ρ eig hρ hρsum hx
    obtain ⟨a, _⟩ := exists_pos_spectral_weight (fun a => (hρ a).le) hρsum
    have hbl : 0 < finiteInverse ρ eig hρ hρsum x - l := by linarith [hl a, hs.1 a]
    have hlow := le_finiteResolvent (fun a => (hρ a).le) hρsum hl hs.1
    rw [hs.2] at hlow
    have hlow' := (div_le_iff₀ hbl).mp hlow
    have hlow'' : 1 / x ≤ finiteInverse ρ eig hρ hρsum x - l := by
      apply (div_le_iff₀ hx).mpr
      nlinarith
    refine ⟨by linarith, ?_⟩
    by_cases hbu : finiteInverse ρ eig hρ hρsum x ≤ u
    · linarith [one_div_pos.mpr hx]
    · exact (finiteR_bounds (fun a => (hρ a).le) hρsum hl hu
        (lt_of_not_ge hbu) hx hs.2).2
  · simp only [finiteR, ite_eq_right hx]
    constructor
    · calc
        l = ∑ a, ρ a * l := by rw [← Finset.sum_mul, hρsum, one_mul]
        _ ≤ ∑ a, ρ a * eig a := Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (hl a) (hρ a).le
    · calc
        (∑ a, ρ a * eig a) ≤ ∑ a, ρ a * u := Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (hu a) (hρ a).le
        _ = u := by rw [← Finset.sum_mul, hρsum, one_mul]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quantitative estimate at zero for the finite spectral transform. -/

noncomputable section

open scoped BigOperators Topology
open Filter Set

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

/-- An exact remainder identity for the finite inverse resolvent. -/
theorem finiteR_sub_mean (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 < x) :
    finiteR ρ eig hρ hρsum x - ∑ a, ρ a * eig a =
      ∑ a, ρ a * (finiteR ρ eig hρ hρsum x - eig a) ^ 2 /
        (finiteInverse ρ eig hρ hρsum x - eig a) := by
  let b := finiteInverse ρ eig hρ hρsum x
  have hs := finiteInverse_spec ρ eig hρ hρsum hx
  have hterm : ∀ a,
      ρ a * (b - 1 / x - eig a) ^ 2 / (b - eig a) =
        ρ a * (b - eig a) - (2 / x) * ρ a +
          (1 / x ^ 2) * (ρ a / (b - eig a)) := by
    intro a
    have hba : b - eig a ≠ 0 := (sub_pos.mpr (hs.1 a)).ne'
    field_simp [hx.ne', hba]
    ring
  simp only [finiteR, ite_eq_left hx]
  change b - 1 / x - ∑ a, ρ a * eig a =
    ∑ a, ρ a * (b - 1 / x - eig a) ^ 2 / (b - eig a)
  simp_rw [hterm, mul_sub]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, hρsum, one_mul, mul_one]
  change b - 1 / x - ∑ a, ρ a * eig a =
    b - ∑ a, ρ a * eig a - 2 / x + (1 / x ^ 2) * finiteResolvent ρ eig b
  rw [hs.2]
  field_simp
  ring

theorem mean_le_finiteR (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 < x) :
    (∑ a, ρ a * eig a) ≤ finiteR ρ eig hρ hρsum x := by
  have hs := finiteInverse_spec ρ eig hρ hρsum hx
  apply sub_nonneg.mp
  rw [finiteR_sub_mean ρ eig hρ hρsum hx]
  exact Finset.sum_nonneg fun a _ => div_nonneg
    (mul_nonneg (hρ a).le (sq_nonneg _)) (sub_pos.mpr (hs.1 a)).le

/-- The uniform `O(K²x)` estimate from manuscript `gen:R-at-zero`. -/
theorem finiteR_sub_mean_le (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {K x : ℝ} (_hK : 0 ≤ K)
    (heig : ∀ a, |eig a| ≤ K) (hx : 0 < x) (hsmall : 4 * K * x ≤ 1) :
    finiteR ρ eig hρ hρsum x - ∑ a, ρ a * eig a ≤ 8 * K ^ 2 * x := by
  let b := finiteInverse ρ eig hρ hρsum x
  let r := finiteR ρ eig hρ hρsum x
  have hs := finiteInverse_spec ρ eig hρ hρsum hx
  have hr := finiteR_mem_interval ρ eig hρ hρsum
    (fun a => (abs_le.mp (heig a)).1) (fun a => (abs_le.mp (heig a)).2) x
  have hbx : x * b = x * r + 1 := by
    dsimp [b, r]
    simp only [finiteR, ite_eq_left hx]
    field_simp
    ring
  have hterm : ∀ a, ρ a * (r - eig a) ^ 2 / (b - eig a) ≤ ρ a * (8 * K ^ 2 * x) := by
    intro a
    have he := abs_le.mp (heig a)
    have hsq : (r - eig a) ^ 2 ≤ 4 * K ^ 2 := by
      have hlow : -2 * K ≤ r - eig a := by linarith [hr.1]
      have hupp : r - eig a ≤ 2 * K := by linarith [hr.2]
      have hprod := mul_nonneg (sub_nonneg.mpr hlow) (sub_nonneg.mpr hupp)
      nlinarith
    have hden : 0 < b - eig a := sub_pos.mpr (hs.1 a)
    have hrecip : 1 / (b - eig a) ≤ 2 * x := by
      apply (div_le_iff₀ hden).mpr
      have hrlow : -K ≤ r := hr.1
      have hex : eig a ≤ K := he.2
      have hscaled := mul_le_mul_of_nonneg_left (show -2 * K ≤ r - eig a by linarith) hx.le
      nlinarith
    calc
      ρ a * (r - eig a) ^ 2 / (b - eig a) =
          ρ a * ((r - eig a) ^ 2 * (1 / (b - eig a))) := by ring
      _ ≤ ρ a * (4 * K ^ 2 * (2 * x)) := by
        apply mul_le_mul_of_nonneg_left _ (hρ a).le
        exact mul_le_mul hsq hrecip (one_div_pos.mpr hden).le (by positivity)
      _ = ρ a * (8 * K ^ 2 * x) := by ring
  rw [finiteR_sub_mean ρ eig hρ hρsum hx]
  calc
    (∑ a, ρ a * (r - eig a) ^ 2 / (b - eig a)) ≤
        ∑ a, ρ a * (8 * K ^ 2 * x) := Finset.sum_le_sum fun a _ => hterm a
    _ = 8 * K ^ 2 * x := by rw [← Finset.sum_mul, hρsum, one_mul]

theorem continuousAt_finiteR_zero (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) :
    ContinuousAt (finiteR ρ eig hρ hρsum) 0 := by
  let K := 1 + ∑ a, |eig a|
  have hK : 0 < K := by
    have hsum : 0 ≤ ∑ a, |eig a| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    dsimp [K]
    linarith
  have heig : ∀ a, |eig a| ≤ K := by
    intro a
    have hs : |eig a| ≤ ∑ a, |eig a| :=
      Finset.single_le_sum (f := fun a => |eig a|)
        (fun a _ => abs_nonneg (eig a)) (Finset.mem_univ a)
    dsimp [K]
    linarith
  have ht : Tendsto (fun x : ℝ => 8 * K ^ 2 * |x|) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_abs.tendsto (0 : ℝ)).const_mul (8 * K ^ 2)
  have hevent : ∀ᶠ x : ℝ in 𝓝 0,
      ‖finiteR ρ eig hρ hρsum x - ∑ a, ρ a * eig a‖ ≤ 8 * K ^ 2 * |x| := by
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / (4 * K) by positivity)] with x hxsmall
    rw [Real.norm_eq_abs]
    by_cases hx : 0 < x
    · have hsmall : 4 * K * x ≤ 1 := by
        have h := (lt_div_iff₀ (show (0 : ℝ) < 4 * K by positivity)).mp hxsmall
        nlinarith
      rw [abs_of_nonneg (sub_nonneg.mpr (mean_le_finiteR ρ eig hρ hρsum hx)), abs_of_pos hx]
      exact finiteR_sub_mean_le ρ eig hρ hρsum hK.le heig hx hsmall
    · simp only [finiteR, ite_eq_right hx, sub_self, abs_zero]
      positivity
  have hdiff := squeeze_zero_norm' hevent ht
  have hlim : Tendsto (finiteR ρ eig hρ hρsum) (𝓝 0) (𝓝 (∑ a, ρ a * eig a)) :=
    (tendsto_sub_nhds_zero_iff).mp hdiff
  simpa only [ContinuousAt, finiteR, lt_self_iff_false, ite_false, if_false] using hlim

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

def projectedResolventDerivative (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) (x : ℝ) : ℝ :=
  if 0 < x then ρ a /
    (finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) *
      (finiteInverse ρ eig hρ hρsum x - eig a) ^ 2) else ρ a

theorem projectedResolventDerivative_pos (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) (x : ℝ) :
    0 < projectedResolventDerivative ρ eig hρ hρsum a x := by
  by_cases hx : 0 < x
  · simp only [projectedResolventDerivative, ite_eq_left hx]
    have hs := finiteInverse_spec ρ eig hρ hρsum hx
    exact div_pos (hρ a) (mul_pos
      (finiteSecondResolvent_pos (fun a => (hρ a).le) hρsum hs.1)
      (sq_pos_of_pos (sub_pos.mpr (hs.1 a))))
  · simpa only [projectedResolventDerivative, ite_eq_right hx] using hρ a

theorem sum_projectedResolventDerivative (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (x : ℝ) :
    (∑ a, projectedResolventDerivative ρ eig hρ hρsum a x) = 1 := by
  by_cases hx : 0 < x
  · simp only [projectedResolventDerivative, ite_eq_left hx]
    have hs := finiteInverse_spec ρ eig hρ hρsum hx
    have hm := finiteSecondResolvent_pos (fun a => (hρ a).le) hρsum hs.1
    calc
      _ = (∑ a, ρ a / (finiteInverse ρ eig hρ hρsum x - eig a) ^ 2) /
          finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro a _
        rw [div_div]
        congr 1
        ring
      _ = 1 := div_self hm.ne'
  · simpa only [projectedResolventDerivative, ite_eq_right hx] using hρsum

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint regularity for the finite spectral-group functions. -/

noncomputable section

open scoped BigOperators Topology
open Filter Set

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem projectedResolventDerivative_eq_regular (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {x : ℝ} (hx : 0 ≤ x) :
    projectedResolventDerivative ρ eig hρ hρsum a x = ρ a /
      ((∑ b, ρ b / (1 + x * (finiteR ρ eig hρ hρsum x - eig b)) ^ 2) *
        (1 + x * (finiteR ρ eig hρ hρsum x - eig a)) ^ 2) := by
  rcases hx.eq_or_lt with h | h
  · subst x
    simp only [projectedResolventDerivative, lt_self_iff_false, ite_false, if_false,
      zero_mul, add_zero, one_pow, div_one, hρsum, mul_one]
  · let B := finiteInverse ρ eig hρ hρsum x
    have hs := finiteInverse_spec ρ eig hρ hρsum h
    have hgap : ∀ b, B - eig b ≠ 0 := fun b => (sub_pos.mpr (hs.1 b)).ne'
    have hM := finiteSecondResolvent_pos (fun b => (hρ b).le) hρsum hs.1
    have hden : ∀ b, 1 + x * (finiteR ρ eig hρ hρsum x - eig b) = x * (B - eig b) := by
      intro b
      simp only [finiteR, ite_eq_left h]
      dsimp [B]
      field_simp
      ring
    have hsum : (∑ b, ρ b / (x * (B - eig b)) ^ 2) =
        finiteSecondResolvent ρ eig B / x ^ 2 := by
      unfold finiteSecondResolvent
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro b _
      rw [div_div]
      congr 1
      ring
    simp only [projectedResolventDerivative, ite_eq_left h, hden]
    change ρ a / (finiteSecondResolvent ρ eig B * (B - eig a) ^ 2) = _
    rw [hsum]
    field_simp [h.ne', hM.ne', hgap a]

theorem continuousWithinAt_projectedResolventDerivative_zero
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (a : ι) :
    ContinuousWithinAt (projectedResolventDerivative ρ eig hρ hρsum a) (Ici 0) 0 := by
  let g := fun b x => 1 + x * (finiteR ρ eig hρ hρsum x - eig b)
  have hg : ∀ b, ContinuousAt (g b) 0 := by
    intro b
    exact continuousAt_const.add
      (continuousAt_id.mul ((continuousAt_finiteR_zero ρ eig hρ hρsum).sub continuousAt_const))
  have hS : ContinuousAt (fun x => ∑ b, ρ b / (g b x) ^ 2) 0 := by
    apply tendsto_finsetSum
    intro b _
    exact continuousAt_const.div ((hg b).pow 2) (by simp [g])
  have hc : ContinuousAt (fun x => ρ a / ((∑ b, ρ b / (g b x) ^ 2) * (g a x) ^ 2)) 0 :=
    continuousAt_const.div (hS.mul ((hg a).pow 2)) (by simp [g, hρsum])
  apply hc.continuousWithinAt.congr
  · intro x hx
    exact projectedResolventDerivative_eq_regular ρ eig hρ hρsum a hx
  · exact projectedResolventDerivative_eq_regular ρ eig hρ hρsum a le_rfl

theorem continuousAt_projectedResolventDerivative_pos
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (a : ι)
    {x : ℝ} (hx : 0 < x) :
    ContinuousAt (projectedResolventDerivative ρ eig hρ hρsum a) x := by
  have hs := finiteInverse_spec ρ eig hρ hρsum hx
  have hm := finiteSecondResolvent_pos (fun b => (hρ b).le) hρsum hs.1
  have hcB := (hasStrictDerivAt_finiteInverse ρ eig hρ hρsum hx).hasDerivAt.continuousAt
  have hcM := ((hasStrictDerivAt_finiteSecondResolvent ρ eig hs.1).hasDerivAt.continuousAt).comp hcB
  have hc : ContinuousAt (fun y => ρ a /
      (finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum y) *
        (finiteInverse ρ eig hρ hρsum y - eig a) ^ 2)) x :=
    continuousAt_const.div (hcM.mul ((hcB.sub continuousAt_const).pow 2))
      (mul_ne_zero hm.ne' (pow_ne_zero 2 (sub_pos.mpr (hs.1 a)).ne'))
  apply hc.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  simp only [projectedResolventDerivative, ite_eq_left (show 0 < y from hy)]

theorem continuousOn_projectedResolventDerivative
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (a : ι) {c : ℝ} :
    ContinuousOn (projectedResolventDerivative ρ eig hρ hρsum a) (Icc 0 c) := by
  intro x hx
  rcases hx.1.eq_or_lt with h | h
  · subst x
    exact (continuousWithinAt_projectedResolventDerivative_zero ρ eig hρ hρsum a).mono
      (fun y hy => hy.1)
  · exact (continuousAt_projectedResolventDerivative_pos ρ eig hρ hρsum a h).continuousWithinAt

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

def spectralPathDensity (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) (r : ℝ) : ℝ :=
  projectedResolventDerivative ρ eig hρ hρsum a (deficit p r)

def spectralGroupDiagonal (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) : ℝ :=
  ∫ r in 0..1, spectralPathDensity ρ eig hρ hρsum p a r

theorem spectralPathDensity_nonneg (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) (r : ℝ) :
    0 ≤ spectralPathDensity ρ eig hρ hρsum p a r :=
  (projectedResolventDerivative_pos ρ eig hρ hρsum a (deficit p r)).le

theorem spectralPathDensity_continuousOn (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) :
    ContinuousOn (spectralPathDensity ρ eig hρ hρsum p a) (Icc 0 1) :=
  (continuousOn_projectedResolventDerivative ρ eig hρ hρsum a).comp
    (continuous_deficit p).continuousOn (fun _r hr => deficit_mem_unit p hr)

theorem spectralPathDensity_intervalIntegrable (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) {q : ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (spectralPathDensity ρ eig hρ hρsum p a) volume 0 q :=
  ((spectralPathDensity_continuousOn ρ eig hρ hρsum p a).mono
    (Icc_subset_Icc le_rfl hq.2)).intervalIntegrable_of_Icc hq.1

theorem spectralGroupDiagonal_nonneg (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) :
    0 ≤ spectralGroupDiagonal ρ eig hρ hρsum p a :=
  intervalIntegral.integral_nonneg_of_forall zero_le_one
    (spectralPathDensity_nonneg ρ eig hρ hρsum p a)

theorem sum_spectralGroupDiagonal (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) :
    (∑ a, spectralGroupDiagonal ρ eig hρ hρsum p a) = 1 := by
  unfold spectralGroupDiagonal
  rw [← intervalIntegral.integral_finsetSum
    (fun a _ => spectralPathDensity_intervalIntegrable ρ eig hρ hρsum p a
      ⟨zero_le_one, le_rfl⟩)]
  simp only [spectralPathDensity, sum_projectedResolventDerivative,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]

theorem spectralGroupDiagonal_le_one (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) :
    spectralGroupDiagonal ρ eig hρ hρsum p a ≤ 1 := by
  rw [← sum_spectralGroupDiagonal ρ eig hρ hρsum p]
  exact Finset.single_le_sum (fun b _ => spectralGroupDiagonal_nonneg ρ eig hρ hρsum p b)
    (Finset.mem_univ a)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCanonicalLabels
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical spectral labels as continuous monotone functions of the
total overlap, with the diagonal bound built into their range. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

def cavityCanonicalCoordinate {m : ℕ} (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : Fin m) (t : ℝ) : ℝ :=
  ∫ r in 0..(Set.projIcc 0 1 zero_le_one t : ℝ), spectralPathDensity ρ eig hρ hρsum p a r

lemma cavityCanonicalCoordinate_nonneg {m : ℕ} (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : Fin m) (t : ℝ) :
    0 ≤ cavityCanonicalCoordinate ρ eig hρ hρsum p a t :=
  intervalIntegral.integral_nonneg_of_forall (Set.projIcc 0 1 zero_le_one t).property.1
    (spectralPathDensity_nonneg ρ eig hρ hρsum p a)

lemma cavityCanonicalCoordinate_le_diagonal {m : ℕ} (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : Fin m) (t : ℝ) :
    cavityCanonicalCoordinate ρ eig hρ hρsum p a t ≤ spectralGroupDiagonal ρ eig hρ hρsum p a :=
  intervalIntegral.integral_mono_interval le_rfl (Set.projIcc 0 1 zero_le_one t).property.1
    (Set.projIcc 0 1 zero_le_one t).property.2
    (Eventually.of_forall (spectralPathDensity_nonneg ρ eig hρ hρsum p a))
    (spectralPathDensity_intervalIntegrable ρ eig hρ hρsum p a ⟨zero_le_one, le_rfl⟩)

def cavityCanonicalLabel {m : ℕ} (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : Fin m) (t : ℝ) : Icc (-1 : ℝ) 1 :=
  ⟨cavityCanonicalCoordinate ρ eig hρ hρsum p a t,
    ⟨le_trans (by norm_num) (cavityCanonicalCoordinate_nonneg ρ eig hρ hρsum p a t),
      (cavityCanonicalCoordinate_le_diagonal ρ eig hρ hρsum p a t).trans
        (spectralGroupDiagonal_le_one ρ eig hρ hρsum p a)⟩⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralArrayGG
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

abbrev SpectralEntry (m : ℕ) := Fin m → Set.Icc (-1 : ℝ) 1
abbrev SpectralArray (m : ℕ) := (ℕ × ℕ) → SpectralEntry m
abbrev SpectralBlock (m n : ℕ) := Fin n → Fin n → SpectralEntry m

def spectralBlockView (m n : ℕ) (x : SpectralArray m) : SpectralBlock m n :=
  fun i j => x (i, j)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralReplicaLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual spectral overlap array laws retain the common rotation disorder. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology ENNReal NNReal

namespace InvariantIsing

/-- Keeping the external disorder in the sampled space is essential:
projected overlaps depend on the same rotation as the Gibbs measure. -/
def disorderReplicaLaw {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (P : Measure Ω) (ν : Ω → Measure X)
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)] : Measure (Ω × (ℕ → X)) :=
  P ⊗ₘ replicaKernel ν hν

instance disorderReplicaLaw_probability {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)] :
    IsProbabilityMeasure (disorderReplicaLaw P ν hν) := by
  unfold disorderReplicaLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

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

def spectralCoordinateArray {m : ℕ} (a : Fin m) (x : SpectralArray m) : RealArray :=
  fun i j => x (i,j) a

def SpectralGram {m : ℕ} (x : SpectralArray m) : Prop :=
  ∀ a n, Matrix.PosSemidef (fun i j : Fin n => spectralCoordinateArray a x i j)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralDensityContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous bounded extension of the spectral path density. -/

noncomputable section

open Set Filter
open scoped Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem continuous_projectedResolventDerivative
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (a : ι) :
    Continuous (projectedResolventDerivative ρ eig hρ hρsum a) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hc : ContinuousAt (fun _ : ℝ => ρ a) x := continuousAt_const
    apply hc.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with y hy
    simp only [projectedResolventDerivative,
      ite_eq_right (not_lt.mpr (le_of_lt (show y < 0 from hy)))]
  · subst x
    apply continuousAt_iff_continuous_left_right.mpr
    refine ⟨?_, continuousWithinAt_projectedResolventDerivative_zero ρ eig hρ hρsum a⟩
    have hc : ContinuousWithinAt (fun _ : ℝ => ρ a) (Iic 0) 0 := continuousWithinAt_const
    apply hc.congr
    · intro y hy
      simp only [projectedResolventDerivative, ite_eq_right (not_lt.mpr (show y ≤ 0 from hy))]
    · simp only [projectedResolventDerivative, lt_self_iff_false, ite_false, if_false]
  · exact continuousAt_projectedResolventDerivative_pos ρ eig hρ hρsum a hx

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralPartition
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

def spectralSpinArray {m : ℕ} (x : SpectralArray (m + 1)) : RealArray :=
  fun i j => ∑ a : Fin m, (x (i,j) a.castSucc : ℝ)

def SpectralPartitionGeometry (m : ℕ) (x : SpectralArray (m + 1)) : Prop :=
  (∀ i j, |spectralSpinArray x i j| ≤ 1) ∧ ∀ i, spectralSpinArray x i i = 1

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCascadeSpectralLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Synchronized spectral labels are retained in the finite-cascade
approximation of the scalar GG overlap law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

def cavitySynchronizedBlock {m r : ℕ} (d : SpectralEntry m)
    (f : Fin m → ℝ → Icc (-1 : ℝ) 1) (R : Fin r → Fin r → ℝ) : SpectralBlock m r :=
  fun i j a => if i = j then d a else f a (R i j)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCanonicalBlockLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical spectral-group blocks of finite cascades converge to the
actual Ward-identified spectral array. The auxiliary tree coordinate is
not needed by these physical group observables. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

def cavitySpectralGroupBlock (m r : ℕ) (x : SpectralArray (m + 1)) : SpectralBlock m r :=
  fun i j a => x (i,j) a.castSucc

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

def cavityGroupGaussianRows (m q : ℕ) : Measure (Fin m → ℕ → Fin q → ℝ) :=
  Measure.pi (fun _ : Fin m => cavityGaussianRows q)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact Gaussian law before orthonormalization. Different fresh
axes are independent; replica covariance is the normalized Gram matrix
of the projected replica vectors. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

namespace InvariantIsing

def cavityProjectionMatrix {n r q : ℕ} (v : Fin r → Fin n → ℝ) :
    Matrix (Fin r × Fin q) (Fin n × Fin q) ℝ :=
  fun a b => if a.2 = b.2 then v a.1 b.1 / Real.sqrt n else 0

def cavityRawProjection {n r q : ℕ} (v : Fin r → Fin n → ℝ)
    (x : ℕ → Fin q → ℝ) : EuclideanSpace ℝ (Fin r × Fin q) :=
  (cavityProjectionMatrix (q := q) v).toEuclideanLin
    (WithLp.toLp 2 (fun p : Fin n × Fin q => x p.1 p.2))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectionLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gram correction leaves the Gaussian projection limit unchanged.
The Slutsky step allows arbitrary dependence between the raw projections
and their normalizing Gram matrix. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

def cavityCorrectProjection {r q : ℕ}
    (y : EuclideanSpace ℝ (Fin r × Fin q)) (C : Matrix (Fin q) (Fin q) ℝ) :
    EuclideanSpace ℝ (Fin r × Fin q) :=
  WithLp.toLp 2 (fun a => ∑ j, y (a.1, j) * C j a.2)

@[simp] lemma cavityCorrectProjection_one {r q : ℕ}
    (y : EuclideanSpace ℝ (Fin r × Fin q)) : cavityCorrectProjection y 1 = y := by
  ext a
  simp [cavityCorrectProjection, Matrix.one_apply]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGroupProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint projections in the independent spectral groups. The output index
retains the group, replica, and fresh-axis coordinates, so the limiting
Gaussian law records independence between different groups. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

def cavityGroupProjectionMatrix {m r q : ℕ} {N : Fin m → ℕ}
    (v : (a : Fin m) → Fin r → Fin (N a) → ℝ) :
    Matrix (Fin m × (Fin r × Fin q)) ((a : Fin m) × (Fin (N a) × Fin q)) ℝ :=
  fun i j => if i.1 = j.1 ∧ i.2.2 = j.2.2 then
    v j.1 i.2.1 j.2.1 / Real.sqrt (N j.1) else 0

def cavityGroupRawProjection {m r q : ℕ} {N : Fin m → ℕ}
    (v : (a : Fin m) → Fin r → Fin (N a) → ℝ)
    (x : Fin m → ℕ → Fin q → ℝ) : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) :=
  (cavityGroupProjectionMatrix v).toEuclideanLin
    (WithLp.toLp 2 (fun j : (a : Fin m) × (Fin (N a) × Fin q) => x j.1 j.2.1 j.2.2))

def cavityGroupCorrectProjection {m r q : ℕ}
    (y : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)))
    (C : Fin m → Matrix (Fin q) (Fin q) ℝ) : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) :=
  WithLp.toLp 2 (fun i => ∑ j, y (i.1, i.2.1, j) * C i.1 j i.2.2)

@[simp] lemma cavityGroupCorrectProjection_one {m r q : ℕ}
    (y : EuclideanSpace ℝ (Fin m × (Fin r × Fin q))) :
    cavityGroupCorrectProjection y (fun _ => 1) = y := by
  ext i
  simp [cavityGroupCorrectProjection, Matrix.one_apply]

def cavityGroupFrameProjection {m r q : ℕ} {N : Fin m → ℕ}
    (v : (a : Fin m) → Fin r → Fin (N a) → ℝ)
    (x : Fin m → ℕ → Fin q → ℝ) : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) :=
  WithLp.toLp 2 (fun i => ∑ k, v i.1 i.2.1 k *
    cavityNormalizeFrame (cavityGaussianMatrix (x i.1) (N i.1)) k i.2.2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGroupCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Covariance identification for the joint spectral-group projection.
Off-group and off-axis covariances vanish, while replica covariances are
the normalized Gram matrices in each eigenspace. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

def cavityGroupReplicaCovariance {m r : ℕ} (q : ℕ)
    (Q : Fin m → Matrix (Fin r) (Fin r) ℝ) :
    Matrix (Fin m × (Fin r × Fin q)) (Fin m × (Fin r × Fin q)) ℝ :=
  fun i j => if i.1 = j.1 ∧ i.2.2 = j.2.2 then Q i.1 i.2.1 j.2.1 else 0

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGroupCovariancePositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity of the actual block covariance for all spectral groups
and all fresh axes. No invertibility is needed. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology BoundedContinuousFunction Matrix

namespace InvariantIsing

def cavitySpectralBlockCovariance {m r : ℕ} (q : ℕ) (ρ : Fin m → ℝ)
    (x : SpectralBlock (m + 1) r) :
    Matrix (Fin m × (Fin r × Fin q)) (Fin m × (Fin r × Fin q)) ℝ :=
  cavityGroupReplicaCovariance q (fun a i j => (x i j a.castSucc : ℝ) / ρ a)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGroupBlockGaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian marking of the physical spectral-group block. The variance
is the projected overlap divided by the group proportion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix

namespace InvariantIsing

def cavityGroupBlockCovariance {m r : ℕ} (q : ℕ) (ρ : Fin m → ℝ)
    (x : SpectralBlock m r) :
    Matrix (Fin m × (Fin r × Fin q)) (Fin m × (Fin r × Fin q)) ℝ :=
  cavityGroupReplicaCovariance q (fun a i j => (x i j a : ℝ) / ρ a)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonal invariance of the finite Gaussian array, expressed as a
simultaneous rotation of all its columns. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InvariantIsing

def cavityColumnEquiv (n q : ℕ) :
    EuclideanSpace ℝ (Fin n × Fin q) ≃ₗᵢ[ℝ]
      PiLp 2 (fun _ : Fin q => EuclideanSpace ℝ (Fin n)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    ((Equiv.prodComm (Fin n) (Fin q)).trans (Equiv.sigmaEquivProd (Fin q) (Fin n)).symm)).trans
    (LinearIsometryEquiv.piLpCurry ℝ 2 (fun (_ : Fin q) (_ : Fin n) => ℝ))

@[simp] lemma cavityColumnEquiv_apply {n q : ℕ}
    (x : EuclideanSpace ℝ (Fin n × Fin q)) (j : Fin q) (k : Fin n) :
    cavityColumnEquiv n q x j k = x (k, j) := rfl

@[simp] lemma cavityColumnEquiv_symm_apply {n q : ℕ}
    (x : PiLp 2 (fun _ : Fin q => EuclideanSpace ℝ (Fin n))) (k : Fin n) (j : Fin q) :
    (cavityColumnEquiv n q).symm x (k, j) = x j k := rfl

def cavityColumnRotation {n : ℕ} (q : ℕ)
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n × Fin q) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n × Fin q) :=
  ((cavityColumnEquiv n q).trans (LinearIsometryEquiv.piLpCongrRight 2 (fun _ => U))).trans
    (cavityColumnEquiv n q).symm

def cavityArrayMatrix (n q : ℕ) (z : EuclideanSpace ℝ (Fin n × Fin q)) :
    Matrix (Fin n) (Fin q) ℝ := fun k j => z (k, j) / Real.sqrt n

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityConditionedFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite conditioned Gaussian construction is an orthonormal frame
and has an exactly orthogonally invariant law. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace InvariantIsing

def cavityArrayGood (n q : ℕ) : Set (EuclideanSpace ℝ (Fin n × Fin q)) :=
  {z | 0 < ((cavityArrayMatrix n q z).transpose * cavityArrayMatrix n q z).det}

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityWindowGram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian Gram matrices compressed to a growing spectral coordinate
window. Prefix differences avoid introducing a second Gaussian array. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix

namespace InvariantIsing

def cavityPrefixGram {N q : ℕ} (A : Matrix (Fin N) (Fin q) ℝ) (l : ℕ) :
    Matrix (Fin q) (Fin q) ℝ :=
  A.transpose * Matrix.diagonal (fun i : Fin N => if i.val < l then (1 : ℝ) else 0) * A

def cavityWindowGram {N q : ℕ} (A : Matrix (Fin N) (Fin q) ℝ) (l u : ℕ) :
    Matrix (Fin q) (Fin q) ℝ := cavityPrefixGram A u - cavityPrefixGram A l

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianRankGram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive definiteness of finite Gaussian and normalized-frame windows. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator NNReal

namespace InvariantIsing

def cavityMaskedRows {N q : ℕ} (A : Matrix (Fin N) (Fin q) ℝ) (l u : ℕ) :
    Matrix (Fin N) (Fin q) ℝ :=
  fun k i => if l ≤ k.val ∧ k.val < u then A k i else 0

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGroupHaarProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The joint Gaussian projection limit for independent Haar frames in
all spectral groups. The exact finite-dimensional law is obtained before
taking limits; no conditional independence is assumed as an extra input. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Topology BoundedContinuousFunction

namespace InvariantIsing

def cavityGroupNormalizedFrames {m q : ℕ} (N : Fin m → ℕ)
    (x : Fin m → ℕ → Fin q → ℝ) : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ :=
  fun a => cavityNormalizeFrame (cavityGaussianMatrix (x a) (N a))

def cavityGroupHaarFrames {m q : ℕ} {N : Fin m → ℕ}
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (U : (a : Fin m) → Orthogonal (N a)) : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ :=
  fun a => (U a : Matrix (Fin (N a)) (Fin (N a)) ℝ) * A₀ a

def cavityGroupMatrixProjection {m r q : ℕ} {N : Fin m → ℕ}
    (v : (a : Fin m) → Fin r → Fin (N a) → ℝ)
    (A : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ) :
    EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) :=
  WithLp.toLp 2 (fun i => ∑ k, v i.1 i.2.1 k * A i.1 k i.2.2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGroupProjectionUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniformity over all bounded spectral-group replica Gram arrays. This
allows the fresh frames to be averaged against the base Gibbs measure. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology Matrix BoundedContinuousFunction

namespace InvariantIsing

def cavityGroupReplicaGram {m r : ℕ} {N : Fin m → ℕ}
    (v : (a : Fin m) → Fin r → Fin (N a) → ℝ) :
    Fin m → Matrix (Fin r) (Fin r) ℝ :=
  fun a i j => (∑ k, v a i k * v a j k) / N a

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarSpectralLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Keep the complete finite spectral overlap block in the Haar
approximation, using its canonical compact embedding into real coordinates. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

def spectralBlockReal {m r : ℕ} (x : SpectralBlock m r) :
    Fin r → Fin r → Fin m → ℝ := fun i j a => x i j a

def spectralBlockClamp {m r : ℕ} (x : Fin r → Fin r → Fin m → ℝ) : SpectralBlock m r :=
  fun i j a => Set.projIcc (-1) 1 (by norm_num) (x i j a)

@[simp] lemma spectralBlockClamp_real {m r : ℕ} (x : SpectralBlock m r) :
    spectralBlockClamp (spectralBlockReal x) = x := by
  funext i j a
  apply Subtype.ext
  simp only [spectralBlockClamp, spectralBlockReal, Set.coe_projIcc]
  rw [min_eq_right (x i j a).property.2, max_eq_right (x i j a).property.1]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarCascadeMatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fresh Haar field and the recalculated finite cascade have matching
bounded spectral-group replica tests. The common limit is identified by GG
and the Ward equations, rather than assumed as an auxiliary cascade law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

def cavityGroupBlockOfBlock {m r : ℕ} (x : SpectralBlock (m + 1) r) : SpectralBlock m r :=
  fun i j a => x i j a.castSucc

@[simp] lemma cavityGroupBlockOfBlock_view {m r : ℕ} (x : SpectralArray (m + 1)) :
    cavityGroupBlockOfBlock (spectralBlockView (m + 1) r x) = cavitySpectralGroupBlock m r x := rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianFactorAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite matrix identities connecting standard-Gaussian square
completion with the original, possibly singular, covariance `B Bᵀ`. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

def cavityFactorPrecision {d : ℕ} (K B : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ := 1 - B.transpose * K * B

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quadratic Gaussian integration through an arbitrary covariance
factor.  The factor may be singular and need not commute with `K`. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

def cavityFactorLinear {d : ℕ} (K B : Matrix (Fin d) (Fin d) ℝ)
    (u : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (B.transpose * K) u

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

theorem continuous_finiteR (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) : Continuous (finiteR ρ eig hρ hρsum) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hc : ContinuousAt (fun _ : ℝ => ∑ a, ρ a * eig a) x := continuousAt_const
    apply hc.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with y hy
    simp only [finiteR, ite_eq_right (not_lt.mpr (le_of_lt (show y < 0 from hy)))]
  · subst x
    exact continuousAt_finiteR_zero ρ eig hρ hρsum
  · exact (hasStrictDerivAt_finiteR ρ eig hρ hρsum hx).hasDerivAt.continuousAt

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The continuous nonnegative right derivative of the finite spectral
R-transform. Its extension at zero is the spectral variance; the constant
extension of `finiteR` to negative arguments is not differentiated there. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

def cavityRDerivative (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (x : ℝ) : ℝ :=
  ∑ a, projectedResolventDerivative rho lam hrho hsum a x *
    (lam a - finiteR rho lam hrho hsum x) ^ 2

lemma cavityRDerivative_nonneg (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (x : ℝ) : 0 ≤ cavityRDerivative rho lam hrho hsum x :=
  Finset.sum_nonneg (fun a _ => mul_nonneg
    (projectedResolventDerivative_pos rho lam hrho hsum a x).le (sq_nonneg _))

lemma continuous_cavityRDerivative (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) : Continuous (cavityRDerivative rho lam hrho hsum) := by
  apply continuous_finsetSum
  intro a _
  exact (continuous_projectedResolventDerivative rho lam hrho hsum a).mul
    ((continuous_const.sub (continuous_finiteR rho lam hrho hsum)).pow 2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityScalarResolventBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform scalar resolvent bounds, including the extension at zero.
The comparison uses any alphabet point above the compressed eigenvalue. -/

noncomputable section
open Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

def cavityScalarResolvent (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (α x : ℝ) : ℝ :=
  x / (1 + x * (finiteR ρ eig hρ hρsum x - α))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityMatrixResolventBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smooth resolvent path of a compressed finite-alphabet matrix.
Its norm bounds depend on the alphabet mass, not on the number of cascade levels. -/

noncomputable section
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator MatrixOrder

namespace InvariantIsing

variable {ι : Type*} [Fintype ι] {d : ℕ}

def cavitySpectralMatrixPath (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian)
    (x : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
    (Matrix.diagonal (fun i => cavityScalarResolvent ρ eig hρ hρsum (hA.eigenvalues i) x))

def cavitySpectralMatrixDensity (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian)
    (x : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
    (Matrix.diagonal (fun i => 1 /
      (finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) *
        (finiteInverse ρ eig hρ hρsum x - hA.eigenvalues i)^2)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityComplement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous local choice of the special complement in the cavity
block: project a limiting frame and orthonormalize its columns. -/

noncomputable section
open Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

def cavityRawComplement {r n d : ℕ} (E : Matrix (Fin r) (Fin n) ℝ)
    (B₀ : Matrix (Fin r) (Fin d) ℝ) : Matrix (Fin r) (Fin d) ℝ :=
  (1 - E * E.transpose) * B₀

def cavityComplement {r n d : ℕ} (E : Matrix (Fin r) (Fin n) ℝ)
    (B₀ : Matrix (Fin r) (Fin d) ℝ) : Matrix (Fin r) (Fin d) ℝ :=
  cavityNormalizeFrame (cavityRawComplement E B₀)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpectralStack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cavity column stack formed from square roots of spectral
compressions. Its columns are orthonormal when the compressions sum to
the identity, and it has the required deterministic limit. -/

noncomputable section
open Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

def cavitySpectralStack {m n : ℕ} (M : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin (m * n)) (Fin n) ℝ := fun i j =>
  CFC.sqrt (M (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2 j

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpecialBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The special/cavity block matrix and its continuous limit. -/

noncomputable section
open Filter
open scoped BigOperators Topology Matrix

namespace InvariantIsing

def cavitySpecialBlocks {r d n : ℕ} (D : Matrix (Fin r) (Fin r) ℝ)
    (B : Matrix (Fin r) (Fin d) ℝ) (E : Matrix (Fin r) (Fin n) ℝ) :
    Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ :=
  Matrix.fromBlocks (B.transpose * D * B) (B.transpose * D * E)
    (E.transpose * D * B) (E.transpose * D * E)

def cavityLimitingStack {m n : ℕ} (ρ : Fin m → ℝ) :
    Matrix (Fin (m * n)) (Fin n) ℝ := fun i j =>
  Real.sqrt (ρ (finProdFinEquiv.symm i).1) *
    (if (finProdFinEquiv.symm i).2 = j then 1 else 0)

def cavityRepeatedSpectrum {m n : ℕ} (lam : Fin m → ℝ) :
    Matrix (Fin (m * n)) (Fin (m * n)) ℝ :=
  Matrix.diagonal (fun i => lam (finProdFinEquiv.symm i).1)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity and precision of the finite-alphabet covariance used by
the cavity calculation. No dimension-dependent spectral bound is needed. -/

noncomputable section
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators

namespace InvariantIsing

variable {ι : Type*} [Fintype ι] {d : ℕ}

def cavityFiniteCovariance (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (g : Fin d → ι) (x : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (finiteInverse rho lam hrho hsum x • 1 - Matrix.diagonal (fun i => lam (g i)))⁻¹

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldMajorantFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The one-step majorant iterated through the actual finite field recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace InvariantIsing

lemma fieldIncrement_tail_positive (h : FieldStep) (i : Fin h.depth) :
    0 < (fieldIncrement h i.succ).1 := by
  change 0 < h.cut i.succ.castSucc
  rw [← h.first]
  apply h.ordered_cut
  change 0 < i.val + 1
  omega

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSpinFolding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact odd-observable law for an even Gaussian tilt. This is the
conditional-spin kernel in the radial field comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma field_abs_tanh_le_one (x : ℝ) : |Real.tanh x| ≤ 1 := by
  rw [Real.tanh_eq, abs_div, abs_of_pos (add_pos (Real.exp_pos _) (Real.exp_pos _))]
  apply (div_le_one (add_pos (Real.exp_pos _) (Real.exp_pos _))).mpr
  exact abs_sub_le_iff.mpr ⟨by linarith [Real.exp_pos (-x)], by linarith [Real.exp_pos x]⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldCommonDepthLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common-prefix depth of the actual finite cascade has the field
partition's interval lengths. The statement allows arbitrary tied values. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

def fieldCommonLevel (h : FieldStep) (σ : ℕ → LabeledLeaf h.depth) : Fin (h.depth + 1) :=
  ⟨labeledCommonDepth h.depth (σ 0) (σ 1),
    Nat.lt_succ_of_le (labeledCommonDepth_le h.depth (σ 0) (σ 1))⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSpinSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual spin sampling and Gaussian transitions for the scalar Ising
recursion. The transition kernels remain probabilities at zero variance. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

def fieldTransitionKernel (ζ : ℝ) (v : ℝ≥0) (F : ℝ → ℝ) (hF : Measurable F) :
    Kernel ℝ ℝ := by
  have hν : Measurable (fun z : ℝ => gaussianReal z v) :=
    measurable_gaussianReal.comp (measurable_id.prodMk measurable_const)
  have hW : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (ζ * F p.2))) :=
    (((hF.comp measurable_snd).const_mul ζ).exp.ennreal_ofReal)
  have hm := measurable_normalizeMass.comp
    (measurable_random_withDensity (ν := fun z : ℝ => gaussianReal z v) hν hW)
  exact ⟨fun z => normalizeMass ((gaussianReal z v).withDensity
    (fun u => ENNReal.ofReal (Real.exp (ζ * F u)))),
      hm⟩

instance fieldTransitionKernel_markov (ζ : ℝ) (v : ℝ≥0)
    (F : ℝ → ℝ) (hF : Measurable F) :
    IsMarkovKernel (fieldTransitionKernel ζ v F hF) :=
  ⟨fun _ => normalizeMass_probability _⟩

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

lemma measurable_field_product {N : ℕ} (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] :
    Measurable (fun z : Fin N → ℝ => Measure.pi (fun i => κ (z i))) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  refine MeasurableSpace.induction_on_inter
    (C := fun s _ => Measurable (fun z : Fin N → ℝ => (Measure.pi (fun i => κ (z i))) s))
    _root_.generateFrom_pi.symm isPiSystem_pi ?_ ?_ ?_ ?_ s hs
  · simp only [measure_empty]
    exact measurable_const
  · rintro s ⟨t, ht, rfl⟩
    simp only [Measure.pi_pi]
    exact Finset.measurable_prod _ fun i _ =>
      (κ.measurable_coe (ht i (mem_univ _))).comp (measurable_pi_apply i)
  · intro s hs ih
    have he (z : Fin N → ℝ) : (Measure.pi (fun i => κ (z i))) sᶜ =
        1 - (Measure.pi (fun i => κ (z i))) s := by
      rw [measure_compl hs (measure_ne_top _ _), measure_univ]
    simp_rw [he]
    exact measurable_const.sub ih
  · intro s hd hs ih
    have he (z : Fin N → ℝ) : (Measure.pi (fun i => κ (z i))) (⋃ n, s n) =
        ∑' n, (Measure.pi (fun i => κ (z i))) (s n) := measure_iUnion hd hs
    simp_rw [he]
    exact Measurable.tsum ih

def fieldVectorTransitionKernel (N : ℕ) (ζ : ℝ) (v : ℝ≥0)
    (F : ℝ → ℝ) (hF : Measurable F) : Kernel (Fin N → ℝ) (Fin N → ℝ) :=
  ⟨fun z => Measure.pi (fun i => fieldTransitionKernel ζ v F hF (z i)),
    measurable_field_product _⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldPublishedPairInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The finite vector log-cosh specialization of Panchenko--Talagrand,
C. R. Acad. Sci. Paris I 345 (2007), 653--656, Section 3, Lemma 3.1,
equation (8), p.655, and Corollary 3.2, equation (9), p.656.

Only bounded measurable tests of the common depth and two endpoint fields
are retained. The statement specifies their law under the actual terminal
tilt, before any spins or overlap expectations are evaluated. The finite
marking theorem supplies this hypothesis.
-/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

def fieldVectorEndpoint (N : ℕ) (h : FieldStep)
    (p : LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ))
    (z : Fin N → ℝ) (α : LabeledLeaf h.depth) : Fin N → ℝ :=
  labeledEnergy h.depth (markForestOfCoords _ h.depth p.2) α z

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldPublishedEvaluation
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

def fieldDepthLevel (h : FieldStep) (d : ℕ) : Fin (h.depth + 1) :=
  ⟨min d h.depth, Nat.lt_succ_of_le (min_le_right _ _)⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteDeficitPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite overlap quantile, held constant beyond its last level,
and the strictly decreasing deficits on its active cascade steps. -/

noncomputable section
open MeasureTheory Set IsingPerceptron

namespace InvariantIsing

def cavityFiniteLevel (n i : ℕ) : Fin (n + 1) :=
  ⟨min i n, Nat.lt_succ_of_le (min_le_right _ _)⟩

@[simp] lemma cavityFiniteLevel_zero (n : ℕ) : cavityFiniteLevel n 0 = 0 := by
  apply Fin.ext
  exact Nat.zero_min _

@[simp] lemma cavityFiniteLevel_last (n : ℕ) : cavityFiniteLevel n n = Fin.last n := by
  apply Fin.ext
  exact min_self _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPrecisionTiltMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Laplace transforms of the positive-precision quadratic Gaussian tilt. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

def cavityPrecisionPotential {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (l z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (‖z‖ ^ 2 - ⟪z, Matrix.toEuclideanCLM (𝕜 := ℝ) Q z⟫) / 2 + ⟪l, z⟫

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityInnovationTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-depth retained Gaussian innovation construction.
The intensity calculation only requires the normalized conditional
fractional moment, not an ordinary exponential moment of a terminal. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal RealInnerProductSpace

namespace InvariantIsing

/-- Retain and rescale each Gaussian mark while updating the running
sum by the original increment. -/
def cavityInnovationTree {d : ℕ} : (n : ℕ) → (ℕ → ℝ) →
    (ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) →
    (ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ) →
    (ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) →
    EuclideanSpace ℝ (Fin d) → NoiseTree (EuclideanSpace ℝ (Fin d)) n →
      NoiseTree (EuclideanSpace ℝ (Fin d)) n
  | 0, _, _, _, _, _, _ => PUnit.unit
  | n + 1, b, μ, c, g, s, T =>
      (sigmaPart ((powerIntensity (b 0)).prod ((μ 0 : Measure _).prod
        (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n (fun j => b (j + 1))
          (fun j => μ (j + 1))))) T).map
        (fun p => (c 0 (s, p.2.1) * p.1, (g 0 (s, p.2.1),
          cavityInnovationTree n (fun j => b (j + 1)) (fun j => μ (j + 1))
            (fun j => c (j + 1)) (fun j => g (j + 1)) (s + p.2.1) p.2.2)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityQuadraticStepWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial weights for the quadratic cascade recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

def cavityQuadraticStepWeight {d : ℕ} (K P C : Matrix (Fin d) (Fin d) ℝ) (ζ : ℝ)
    (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.exp (⟪p.1 + p.2, Matrix.toEuclideanCLM (𝕜 := ℝ)
    (cavityBackwardQuadratic K C) (p.1 + p.2)⟫ / 2 -
    ⟪p.1, Matrix.toEuclideanCLM (𝕜 := ℝ) (cavityBackwardQuadratic K P) p.1⟫ / 2 +
    Real.log ((1 - P * K).det / (1 - C * K).det) / (2 * ζ))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityQuadraticTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent Gaussian innovations for the retained finite quadratic tree. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

def cavityGaussianMarks {d : ℕ} (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (i : ℕ) : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) :=
  ⟨multivariateGaussian 0 (S i), (by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

def cavityStepInnovation {d : ℕ} (K P C : Matrix (Fin d) (Fin d) ℝ)
    (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - C * K)⁻¹ (p.1 + p.2) -
    Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - P * K)⁻¹ p.1

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityInnovationLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Leaf transport for the retained quadratic innovation tree. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal

namespace InvariantIsing

def cavityInnovationLeaf {d : ℕ} : (n : ℕ) →
    (ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ) →
    (ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) →
    EuclideanSpace ℝ (Fin d) → NoiseLeaf (EuclideanSpace ℝ (Fin d)) n →
      NoiseLeaf (EuclideanSpace ℝ (Fin d)) n
  | 0, _, _, _, _ => PUnit.unit
  | n + 1, c, g, s, v => (c 0 (s, v.2.1) * v.1, (g 0 (s, v.2.1),
      cavityInnovationLeaf n (fun i => c (i + 1)) (fun i => g (i + 1))
        (s + v.2.1) v.2.2))

def cavityLeafSum {d : ℕ} : (n : ℕ) → EuclideanSpace ℝ (Fin d) →
    NoiseLeaf (EuclideanSpace ℝ (Fin d)) n → EuclideanSpace ℝ (Fin d)
  | 0, s, _ => s
  | n + 1, s, v => cavityLeafSum n (s + v.2.1) v.2.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityInnovationPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quadratic innovation change preserves shared Gaussian prefixes.
This is the deterministic part of transporting common-level spin tests. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix Classical

namespace InvariantIsing

def cavityCommonMarkDepth {A : Type} :
    (n : ℕ) → NoiseLeaf A n → NoiseLeaf A n → ℕ
  | 0, _, _ => 0
  | n + 1, v, w => if v.2.1 = w.2.1 then cavityCommonMarkDepth n v.2.2 w.2.2 + 1 else 0

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityQuadraticNormalizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite quadratic cascade normalizer from its conditional moments. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

def cavityDeterminantStep {d : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (H : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ) (i : ℕ) : ℝ :=
  Real.log ((1 - H i * K).det / (1 - H (i + 1) * K).det) / (2 * b i)

def cavityQuadraticValue {d : ℕ} (n : ℕ) (K : Matrix (Fin d) (Fin d) ℝ)
    (H : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ) (i : ℕ)
    (s : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ⟪s, Matrix.toEuclideanCLM (𝕜 := ℝ) (cavityBackwardQuadratic K (H i)) s⟫ / 2 +
    ∑ j ∈ Finset.range i, cavityDeterminantStep K H b j -
    ∑ j ∈ Finset.range n, cavityDeterminantStep K H b j

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianNodeLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite projections of independent Gaussian nodes. Repeated use of a
node retains its covariance, as required by the shared prefixes of replicas. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators RealInnerProductSpace

namespace InvariantIsing

variable {d r : ℕ}

def cavityGaussianNodeSum {J : Type*} [Fintype J]
    (w : Fin r → J → ℝ) (z : J → EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin r × Fin d) :=
  WithLp.toLp 2 (fun p => ∑ a, w p.1 a * z a p.2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianNodeCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The covariance of a finite linear Gaussian node projection is
positive semidefinite directly from its independent node covariances. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators

namespace InvariantIsing

def cavityGaussianNodeCovariance {J : Type*} [Fintype J] {r d : ℕ}
    (S : J → Matrix (Fin d) (Fin d) ℝ) (w : Fin r → J → ℝ) :
    Matrix (Fin r × Fin d) (Fin r × Fin d) ℝ :=
  fun p q => ∑ a, w p.1 a * w q.1 a * S a p.2 q.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityResidualPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The residual-integrated partition function in `cav:q-constants`. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

/-- The final Gaussian integral is an ordinary residual at each leaf,
not an additional Poisson level. -/
def cavityResidualPartition {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (s : EuclideanSpace ℝ (Fin d))
    (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n) : ℝ≥0∞ :=
  ∫⁻ v, ∫⁻ z : EuclideanSpace ℝ (Fin d),
    ENNReal.ofReal (Real.exp (⟪cavityLeafSum n s v + z,
      Matrix.toEuclideanCLM (𝕜 := ℝ) K (cavityLeafSum n s v + z)⟫ / 2))
      ∂multivariateGaussian 0 R ∂noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityResidualFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity and finiteness of the actual residual-integrated normalizer. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

lemma measurable_cavityLeafSum_joint {d : ℕ} (n : ℕ) :
    Measurable (fun p : EuclideanSpace ℝ (Fin d) × NoiseLeaf (EuclideanSpace ℝ (Fin d)) n =>
      cavityLeafSum n p.1 p.2) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
    exact ih.comp ((measurable_fst.add measurable_snd.snd.fst).prodMk
      measurable_snd.snd.snd)

lemma measurable_cavityLeafSum {d : ℕ} (n : ℕ) (s : EuclideanSpace ℝ (Fin d)) :
    Measurable (cavityLeafSum n s) :=
  (measurable_cavityLeafSum_joint n).comp (measurable_const.prodMk measurable_id)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityResidualInnovation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The joint innovation map for a true cascade leaf and its ordinary
terminal residual. All residual randomness remains outside the cascade. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

def cavityQuadraticResidualGibbs {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (s : EuclideanSpace ℝ (Fin d))
    (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n) :
    Measure (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d)) :=
  normalizeMass (((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V).prod
    (multivariateGaussian 0 R)).withDensity
      (fun p => ENNReal.ofReal (Real.exp (⟪cavityLeafSum n s p.1 + p.2,
        Matrix.toEuclideanCLM (𝕜 := ℝ) K (cavityLeafSum n s p.1 + p.2)⟫ / 2))))

instance cavityQuadraticResidualGibbs_probability {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (s : EuclideanSpace ℝ (Fin d))
    (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n) :
    IsProbabilityMeasure (cavityQuadraticResidualGibbs n K R s V) :=
  normalizeMass_probability _

def cavityResidualInnovationMap {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (s : EuclideanSpace ℝ (Fin d))
    (p : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d)) :
    NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d) :=
  (cavityInnovationLeaf n
    (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
    (fun i => cavityStepInnovation K (H i) (H (i + 1))) s p.1,
    cavityLeafSum n s p.1 + p.2 -
      Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H n * K)⁻¹ (cavityLeafSum n s p.1))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectedForest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Projection of the retained Gaussian forest to the independent cavity fields. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix BigOperators NNReal

namespace InvariantIsing

def cavityProjectField {d k : ℕ} (L : Matrix (Fin d) (Fin k) ℝ)
    (z : EuclideanSpace ℝ (Fin d)) : Fin k → ℝ :=
  WithLp.ofLp (L.transpose.toEuclideanLin.toContinuousLinearMap z)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianCoordinateMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite coordinate projection needed to select the physical
special axes from the Gaussian spectral-group block. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators

namespace InvariantIsing

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def cavityGaussianCoordinateMap (e : J → I) (z : EuclideanSpace ℝ I) :
    EuclideanSpace ℝ J := WithLp.toLp 2 (fun j => z (e j))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteGroupSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selecting the assigned special axes from the Gaussian spectral-group
block gives precisely the finite cavity field law. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped Matrix BigOperators

namespace InvariantIsing

def cavitySelectedGroupIndex {m d r k : ℕ} (e : Fin d → Fin m × Fin k)
    (u : Fin r × Fin d) : Fin m × (Fin r × Fin k) :=
  ((e u.2).1, (u.1, (e u.2).2))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityReplicaGaussianAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded replica tests may be averaged over the actual Gaussian
root and forest before, or after, sampling the labeled leaves. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix BigOperators

namespace InvariantIsing

def cavityReplicaField {r d : ℕ} (n : ℕ) (T : LabeledTree n)
    (σ : Fin r → LabeledLeaf n)
    (z : (EuclideanSpace ℝ (Fin d) × (ForestVertex n → EuclideanSpace ℝ (Fin d))) ×
      (Fin r → EuclideanSpace ℝ (Fin d))) : EuclideanSpace ℝ (Fin r × Fin d) :=
  WithLp.toLp 2 (fun u =>
    (cavityLeafSum n z.1.1 (labeledNoiseLeaf _ n
      (T, markForestOfCoords _ n z.1.2) (σ u.1)) + z.2 u.1) u.2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySelectedReplicaTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable tests of the physical selected axes can be evaluated
under the original finite Gaussian root/forest/residual law. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped Matrix BigOperators

namespace InvariantIsing

def cavitySelectedGroupProjection {m d r k : ℕ} (e : Fin d → Fin m × Fin k) :
    EuclideanSpace ℝ (Fin m × (Fin r × Fin k)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin d)) :=
  ContinuousLinearMap.pi (fun i =>
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap).comp
      (ContinuousLinearMap.pi (fun a => EuclideanSpace.proj (cavitySelectedGroupIndex e (i, a)))))

@[simp] lemma cavitySelectedGroupProjection_apply {m d r k : ℕ}
    (e : Fin d → Fin m × Fin k)
    (z : EuclideanSpace ℝ (Fin m × (Fin r × Fin k))) (i : Fin r) (a : Fin d) :
    cavitySelectedGroupProjection e z i a = z (cavitySelectedGroupIndex e (i, a)) := rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLabeledModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite cavity model in a fixed measurable state space:
the tree, Gaussian root and forest are disorder; the leaf, ordinary
residual and Ising spin form the configuration. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix BigOperators

namespace InvariantIsing

def cavityLabeledLeafKernel (n : ℕ) : Kernel (LabeledTree n) (LabeledLeaf n) :=
  ⟨labeledLeafLaw n, measurable_labeledLeafLaw n⟩

instance cavityLabeledLeafKernel_markov (n : ℕ) : IsMarkovKernel (cavityLabeledLeafKernel n) :=
  ⟨fun T => inferInstanceAs (IsProbabilityMeasure (labeledLeafLaw n T))⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectedSpinNumerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact spin-prior numerators for the selected physical Haar projections.
The shared projection matrix remains outside the replica product measure. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

def cavitySelectedSiteProjection {m q d : ℕ} {N : Fin m → ℕ} {X : Type*}
    (e : Fin d → Fin m × Fin q) (v : (a : Fin m) → X → Fin (N a) → ℝ)
    (A : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ) (x : X) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j => ∑ l, v (e j).1 x l * A (e j).1 l (e j).2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPhysicalFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cavity exponent difference in the original coordinates. The
retained interaction cancels; only the special and cavity projections
enter the factor. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

def cavityPhysicalChange {r d n : ℕ}
    (V : Matrix (Fin r) (Fin d) ℝ) (E : Matrix (Fin r) (Fin n) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  V * K * V.transpose + V * L * E.transpose +
    (V * L * E.transpose).transpose + E * C * E.transpose

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityMeasurableComplement
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A global measurable completion of the cavity columns. The rule first
tries the prescribed limiting frame and otherwise uses a fixed dense
sequence. Near the limit it agrees with the continuous local rule. -/

noncomputable section
open MeasureTheory Filter TopologicalSpace
open scoped Matrix Topology MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

def cavityComplementCandidate {d n : ℕ}
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ) : ℕ → Matrix (Fin (d + n)) (Fin d) ℝ
  | 0 => B₀
  | k + 1 => denseSeq (Fin (d + n) → Fin d → ℝ) k

def cavityGoodCandidate {d n : ℕ} (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ)
    (E : Matrix (Fin (d + n)) (Fin n) ℝ) (k : ℕ) : Prop :=
  0 < ((cavityRawComplement E (cavityComplementCandidate B₀ k)).transpose *
    cavityRawComplement E (cavityComplementCandidate B₀ k)).det

def cavityComplementChoicePredicate {d n : ℕ}
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ)
    (E : Matrix (Fin (d + n)) (Fin n) ℝ) (k : ℕ) : Prop :=
  if k = 0 then ¬∃ j, cavityGoodCandidate B₀ E j else cavityGoodCandidate B₀ E (k - 1)

lemma cavityComplementChoice_exists {d n : ℕ}
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ)
    (E : Matrix (Fin (d + n)) (Fin n) ℝ) :
    ∃ k, cavityComplementChoicePredicate B₀ E k := by
  classical
  by_cases h : ∃ j, cavityGoodCandidate B₀ E j
  · obtain ⟨j, hj⟩ := h
    exact ⟨j + 1, by simpa [cavityComplementChoicePredicate] using hj⟩
  · exact ⟨0, by simpa [cavityComplementChoicePredicate] using h⟩

def cavitySelectedComplement {d n : ℕ}
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ)
    (E : Matrix (Fin (d + n)) (Fin n) ℝ) : Matrix (Fin (d + n)) (Fin d) ℝ :=
  by classical exact cavityComplement E (cavityComplementCandidate B₀
    (Nat.find (cavityComplementChoice_exists B₀ E) - 1))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCouplingAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The orthogonal spectral directions in the finite cavity coupling.
Each spectral image of the cavity columns is normalized separately.
The resulting frame carries the small square-root stack isometrically
back to the original cavity columns. -/

noncomputable section
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

def cavityEigenspaceFrame {r m n : ℕ}
    (X : Fin m → Matrix (Fin r) (Fin n) ℝ) : Matrix (Fin r) (Fin (m * n)) ℝ :=
  fun i j => cavityNormalizeFrame (X (finProdFinEquiv.symm j).1)
    i (finProdFinEquiv.symm j).2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpectralImages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The separate spectral images of the cavity columns. These are the
concrete inputs to the normalized-frame coupling construction. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

def cavitySpectralImage {r m n : ℕ} (g : Fin r → Fin m)
    (A : Matrix (Fin r) (Fin n) ℝ) (a : Fin m) : Matrix (Fin r) (Fin n) ℝ :=
  fun i j => if g i = a then A i j else 0

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRetainedFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete the cavity directions inside each spectral group. The added
columns are retained eigenvectors supported in the same group. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

def cavityGroupLift {r m q t : ℕ} (g : Fin r → Fin m) (a : Fin m)
    (e : {i : Fin r // g i = a} ≃ Fin q) (B : Matrix (Fin q) (Fin t) ℝ) :
    Matrix (Fin r) (Fin t) ℝ :=
  fun i j => if hi : g i = a then B (e ⟨i, hi⟩) j else 0

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBaseReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact removal and replacement of the small spectral block. The base
matrix is defined without choosing bases in the retained eigenspaces. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

def cavityBaseReplacement {r s d : ℕ}
    (J : Matrix (Fin r) (Fin r) ℝ) (W : Matrix (Fin r) (Fin s) ℝ)
    (D : Matrix (Fin s) (Fin s) ℝ) (B : Matrix (Fin s) (Fin d) ℝ)
    (A₀ : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  J - W * D * W.transpose + (W * B) * A₀ * (W * B).transpose

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRetainedStack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble the retained group frames without imposing equal group
sizes. The separate group projector identities give completeness. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

def cavityRetainedStack {r m : ℕ} (k : Fin m → ℕ)
    (R : (a : Fin m) → Matrix (Fin r) (Fin (k a)) ℝ) :
    Matrix (Fin r) ((a : Fin m) × Fin (k a)) ℝ := fun i j => R j.1 i j.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityReservoirFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An orthonormal base frame perpendicular to the physical cavity
coordinates gives an orthogonal eigenbasis of the reservoir. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

def cavityReservoirRows {N n : ℕ} {ι : Type*}
    (F : Matrix (Fin (N + n)) ι ℝ) : Matrix (Fin N) ι ℝ :=
  fun i j => F (i.castAdd n) j

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityReservoirRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reservoir rotations fix the physical cavity columns exactly. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

def cavityReservoirRotation {N n : ℕ} (V : Orthogonal N) : Orthogonal (N + n) := by
  let D : Matrix (Fin N ⊕ Fin n) (Fin N ⊕ Fin n) ℝ :=
    Matrix.fromBlocks (V : Matrix (Fin N) (Fin N) ℝ) 0 0 1
  let e : Fin N ⊕ Fin n ≃ Fin (N + n) := finSumFinEquiv
  refine ⟨D.submatrix e.symm e.symm, (Matrix.mem_orthogonalGroup_iff' _ ℝ).mpr ?_⟩
  change D.transpose.submatrix e.symm e.symm * D.submatrix e.symm e.symm = 1
  rw [Matrix.submatrix_mul_equiv]
  have hD : D.transpose * D = 1 := by
    have hV := (Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mp V.property
    simp only [D, Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.transpose_one,
      Matrix.fromBlocks_multiply, hV, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.one_mul, Matrix.fromBlocks_one]
  rw [hD, Matrix.submatrix_one_equiv]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPhysicalBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable base interaction built from the actual cavity columns. -/

noncomputable section
open MeasureTheory
open scoped Matrix

namespace InvariantIsing

def cavityColumns {N n : ℕ} (U : Orthogonal (N + n)) :
    Matrix (Fin (N + n)) (Fin n) ℝ :=
  fun i j => (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) i (Fin.natAdd N j)

def cavityCompressionGrams {N n m : ℕ} (g : Fin (N + n) → Fin m)
    (U : Orthogonal (N + n)) : Fin m → Matrix (Fin n) (Fin n) ℝ :=
  fun a => (cavitySpectralImage g (cavityColumns U) a).transpose *
    cavitySpectralImage g (cavityColumns U) a

def cavityPhysicalBase {N n m d : ℕ} (g : Fin (N + n) → Fin m) (lam : Fin m → ℝ)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (A₀ : Matrix (Fin d) (Fin d) ℝ) (U : Orthogonal (N + n)) :
    Matrix (Fin N) (Fin N) ℝ :=
  ((U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose *
    cavityBaseReplacement (Matrix.diagonal (fun i => lam (g i)))
      (cavityEigenspaceFrame (cavitySpectralImage g (cavityColumns U)))
      (cavityRepeatedSpectrum (n := n) lam) (B (cavityCompressionGrams g U)) A₀ *
    (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)).submatrix
      (Fin.castAdd n) (Fin.castAdd n)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityComparisonRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dimension-dependent errors in the finite cavity comparison.
The geometric cutoff is retained with its full Gaussian amplitude. -/

noncomputable section
open IsingPerceptron Filter
open scoped BigOperators Topology

namespace InvariantIsing

def cavityWeightedKernel (N : ℕ) (u K : ℕ → ℝ) : ℝ :=
  ∑ j : Fin N, perturbationWeight j ^ 2 * u j ^ 2 * K j

def cavityCovarianceRate (n : ℕ) (C : ℝ) (N : ℕ) : ℝ :=
  4 * |(N + n) * perturbationScale (N + n) ^ 2 - N * perturbationScale N ^ 2| +
    4 * C * perturbationScale N ^ 2 +
    4 * ((N + n) * perturbationScale (N + n) ^ 2 * (1 / 2 : ℝ) ^ N)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_PlaneRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth coordinate-plane rotations for the finite Haar Ward calculation. -/

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace InvariantIsing

/-- Generator with xᵢ'=xⱼ and xⱼ'=-xᵢ. -/
def planeGenerator {N : ℕ} (i j : Fin N) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.single i j 1 - Matrix.single j i 1

lemma planeGenerator_skew {N : ℕ} (i j : Fin N) :
    planeGenerator i j ∈ skewAdjoint (Matrix (Fin N) (Fin N) ℝ) := by
  rw [skewAdjoint.mem_iff]
  simp [planeGenerator, Matrix.star_eq_conjTranspose]

/-- The exponential of the plane generator is orthogonal. -/
def planeRotation {N : ℕ} (i j : Fin N) (t : ℝ) : Orthogonal N :=
  ⟨NormedSpace.exp (t • planeGenerator i j),
    NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
      (by simpa only [skewAdjoint.mem_iff, star_smul, star_trivial, smul_neg] using
        congrArg (fun M => t • M) (skewAdjoint.mem_iff.mp (planeGenerator_skew i j)))⟩

@[simp] lemma planeRotation_zero {N : ℕ} (i j : Fin N) : planeRotation i j 0 = 1 := by
  apply Subtype.ext
  simp [planeRotation]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_SpecialPlaneRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Genuine coordinate-plane rotations and infinitesimal Haar invariance on
`SO(N)`, the rotation group used by the actual enriched model. -/

noncomputable section

open MeasureTheory Filter IsingPerceptron
open scoped Topology Matrix Matrix.Norms.Frobenius

namespace InvariantIsing

/-- Forget only the determinant-one condition. -/
def specialToOrthogonal {N : ℕ} : SpecialOrthogonal N →* Orthogonal N where
  toFun U := ⟨U.val, (Matrix.mem_specialOrthogonalGroup_iff.mp U.property).1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] lemma matrixRotation_specialToOrthogonal {N : ℕ} (U : SpecialOrthogonal N) :
    matrixRotation (specialToOrthogonal U) = specialRotation U := rfl

/-- Orthogonal determinants have only two possible real values. -/
lemma orthogonal_det_eq_one_or_neg_one {N : ℕ} (U : Orthogonal N) :
    (U : Matrix (Fin N) (Fin N) ℝ).det = 1 ∨
      (U : Matrix (Fin N) (Fin N) ℝ).det = -1 := by
  apply mul_self_eq_one_iff.mp
  have h := congrArg Matrix.det ((Matrix.mem_orthogonalGroup_iff (Fin N) ℝ).mp U.property)
  simpa only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] using h

/-- A continuous plane-rotation path starts at determinant one and cannot
switch between the two orthogonal determinant values. -/
lemma planeRotation_det {N : ℕ} (i j : Fin N) (t : ℝ) :
    (planeRotation i j t : Matrix (Fin N) (Fin N) ℝ).det = 1 := by
  let f : ℝ → ℝ := fun s => (planeRotation i j s : Matrix (Fin N) (Fin N) ℝ).det
  have hc : Continuous f := by
    apply Continuous.matrix_det
    exact continuous_iff_continuousAt.mpr fun s =>
      (hasDerivAt_exp_smul_const' (planeGenerator i j) s).continuousAt
  have hm : Set.MapsTo f Set.univ ({1, -1} : Set ℝ) := by
    intro s _
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, f] using
      orthogonal_det_eq_one_or_neg_one (planeRotation i j s)
  have he : f t = f 0 := isPreconnected_univ.constant_of_mapsTo
    (Set.toFinite ({1, -1} : Set ℝ)).isDiscrete hc.continuousOn hm (Set.mem_univ t)
      (Set.mem_univ 0)
  simpa only [f, planeRotation_zero, OneMemClass.coe_one, Matrix.det_one] using he

/-- The same matrix exponential, now as an element of the special orthogonal group. -/
def specialPlaneRotation {N : ℕ} (i j : Fin N) (t : ℝ) : SpecialOrthogonal N :=
  ⟨(planeRotation i j t).val,
    Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨(planeRotation i j t).property, planeRotation_det i j t⟩⟩

@[simp] lemma specialPlaneRotation_zero {N : ℕ} (i j : Fin N) :
    specialPlaneRotation i j 0 = 1 := by
  apply Subtype.ext
  change (planeRotation i j 0 : Matrix (Fin N) (Fin N) ℝ) = 1
  simp only [planeRotation_zero, OneMemClass.coe_one]

@[simp] lemma specialToOrthogonal_planeRotation {N : ℕ} (i j : Fin N) (t : ℝ) :
    specialToOrthogonal (specialPlaneRotation i j t) = planeRotation i j t := rfl


end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_ThermalPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Temperature differentiation for the actual finite Ising pressure. -/

noncomputable section

open IsingPerceptron MeasureTheory Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma GibbsReference_one {S : Type*} [Nonempty S] :
    GibbsReference (fun _ : S => (1 : ℝ)) :=
  ⟨fun _ => zero_le_one, ⟨Classical.choice inferInstance, zero_lt_one⟩⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpinIsometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Signed site permutations act on the actual Ising cube and its
projected overlaps. Their pair-spin observables have no sign factor. -/

noncomputable section
open IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

def cavityPermutationFlip {N : ℕ} (hN : 0 < N) (p : Equiv.Perm (Fin N))
    (i : Fin N) : Bool := decide (i = ⟨0, hN⟩ ∧ (p.permMatrix ℝ).det = -1)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPhysicalProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical spectral projections and their exact signed-site action. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Matrix

namespace InvariantIsing

def cavitySpectralProjection {N : ℕ} (U : Rotation N) (I : Finset (Fin N))
    (x : EuclideanSpace ℝ (Fin N)) : EuclideanSpace ℝ (Fin N) :=
  U.symm (WithLp.toLp 2 (fun k => if k ∈ I then U x k else 0))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectionGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unnormalized cavity-column projections are precisely physical
spectral projections at the added sites. -/

noncomputable section
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

def cavitySpecialOrthogonal {N : ℕ} (U : SpecialOrthogonal N) : Orthogonal N :=
  ⟨U.val, (Matrix.mem_specialOrthogonalGroup_iff.mp U.property).1⟩

def cavitySpectralGroup {N m : ℕ} (g : Fin N → Fin m) (a : Fin m) : Finset (Fin N) :=
  Finset.univ.filter (fun i => g i = a)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPhysicalFrameOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single reservoir rotation represents both the base interaction
and its selected special axes, as needed for the fresh-frame law. -/

noncomputable section
open scoped Matrix BigOperators

namespace InvariantIsing

def cavityCanonicalSpecial {N d : ℕ} {ι : Type*} (e : (ι ⊕ Fin d) ≃ Fin N) :
    Matrix (Fin N) (Fin d) ℝ := fun i j => if i = e (Sum.inr j) then 1 else 0

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityConcreteFrameOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual base interaction and special axes belong jointly to a
single prescribed Haar orbit, not merely to separate marginal orbits. -/

noncomputable section
open MeasureTheory
open scoped Matrix BigOperators

namespace InvariantIsing

def cavityPhysicalSpecial {N n m d : ℕ} (g : Fin (N + n) → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (U : Orthogonal (N + n)) : Matrix (Fin N) (Fin d) ℝ :=
  cavityReservoirRows ((U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose *
    (cavityEigenspaceFrame (cavitySpectralImage g (cavityColumns U)) *
      B (cavityCompressionGrams g U)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBaseHaarFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact independence, in bounded-test form, of the Haar base spectral
orbit and the small compression data in the concrete cavity coupling. -/

noncomputable section
open MeasureTheory
open scoped Matrix

namespace InvariantIsing

def cavityConjugate {N : ℕ} (V : Orthogonal N) (J : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  (V : Matrix (Fin N) (Fin N) ℝ) * J * (V : Matrix (Fin N) (Fin N) ℝ).transpose

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCompressionBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint Haar compression limits for the actual measurable cavity block
construction. Only continuity at the prescribed limiting stack is used;
the completion rule need not be continuous on every frame. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator
  BoundedContinuousFunction

namespace InvariantIsing

def cavityReindexedStack {m n d : ℕ} (e : Fin (m * n) ≃ Fin (d + n))
    (M : Fin m → Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin (d + n)) (Fin n) ℝ :=
  fun i j => cavitySpectralStack M (e.symm i) j

def cavityCompressionBlocks {m n d : ℕ} (e : Fin (m * n) ≃ Fin (d + n))
    (D : Matrix (Fin (d + n)) (Fin (d + n)) ℝ)
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ)
    (M : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ :=
  cavitySpecialBlocks D (cavitySelectedComplement B₀ (cavityReindexedStack e M))
    (cavityReindexedStack e M)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityConcreteComplement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The measurable special frame used in the actual base interaction.
Its Gram and cavity-orthogonality identities hold for every input frame. -/

noncomputable section
open MeasureTheory
open scoped Matrix BigOperators

namespace InvariantIsing

def cavityConcreteComplement {m n d : ℕ} (e : Fin (m * n) ≃ Fin (d + n))
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ)
    (M : Fin m → Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin (m * n)) (Fin d) ℝ :=
  fun i j => cavitySelectedComplement B₀ (cavityReindexedStack e M) (e i) j

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpectralStabilizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent rotations inside the base spectral groups preserve the
base interaction and rotate its selected frames. -/

noncomputable section
open scoped Matrix BigOperators

namespace InvariantIsing

def cavityGroupRotation {N m : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (U : (a : Fin m) → Orthogonal (k a)) : Orthogonal N := by
  let D := Matrix.blockDiagonal' (fun a => (U a : Matrix (Fin (k a)) (Fin (k a)) ℝ))
  refine ⟨D.submatrix e.symm e.symm, (Matrix.mem_orthogonalGroup_iff' _ ℝ).mpr ?_⟩
  change D.transpose.submatrix e.symm e.symm * D.submatrix e.symm e.symm = 1
  rw [Matrix.submatrix_mul_equiv]
  have hD : D.transpose * D = 1 := by
    simp only [D, Matrix.blockDiagonal'_transpose]
    rw [← Matrix.blockDiagonal'_mul]
    have hU : (fun a => (U a : Matrix (Fin (k a)) (Fin (k a)) ℝ).transpose *
      (U a : Matrix (Fin (k a)) (Fin (k a)) ℝ)) = fun a => (1 : Matrix (Fin (k a)) (Fin (k a)) ℝ) :=
      funext (fun a => (Matrix.mem_orthogonalGroup_iff' (Fin (k a)) ℝ).mp (U a).property)
    rw [hU]
    exact Matrix.blockDiagonal'_one
  rw [hD, Matrix.submatrix_one_equiv]

def cavityGroupFrame {N m : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (a : Fin m) : Matrix (Fin N) (Fin (k a)) ℝ :=
  fun i j => if i = e ⟨a, j⟩ then 1 else 0

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLinearEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform moments of the remaining linear cavity tilt. The estimate uses
only the one-replica exponential radial moment after the quadratic tilt. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Topology

namespace InvariantIsing

def cavityLinearMomentEnvelope (p : ℕ) (c r : ℝ) : ℝ :=
  Real.exp (2 * c + (2 * p + 2 * c + 1) * r)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLinearGaussianMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A covariance bound gives a step-independent moment bound for the
remaining cavity tilt, including singular Gaussian covariance matrices. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

def cavityGaussianLinearMomentBound (d p : ℕ) (c M : ℝ) : ℝ :=
  Real.exp (2 * c) * ∫ z : EuclideanSpace ℝ (Fin d),
    Real.exp (((2 * p + 2 * c + 1) * Real.sqrt M) * ‖z‖) ∂stdGaussian _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityUniformMomentConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constants in the cutoff estimates are uniform over compact sets
of cavity blocks, as required before the geometric limit is taken. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace InvariantIsing

lemma continuous_cavityMatrixMass (d k : ℕ) :
    Continuous (cavityMatrixMass : Matrix (Fin d) (Fin k) ℝ → ℝ) := by
  unfold cavityMatrixMass
  fun_prop

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianRotationCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The trigonometric interpolation between independent Gaussian fields,
with the cavity-size penalty removed along the same path. -/

noncomputable section
open IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def cavityGaussianCurve {X : Type*} {d : ℕ}
    (C A : X → Fin d → ℝ) (t : ℝ) : X → Fin d → ℝ :=
  fun x i => Real.cos t * C x i + Real.sin t * A x i

def cavityGaussianCurveDerivative {X : Type*} {d : ℕ}
    (C A : X → Fin d → ℝ) (t : ℝ) : X → Fin d → ℝ :=
  fun x i => -Real.sin t * C x i + Real.cos t * A x i

def cavityPenaltyCurve {X : Type*} (H V : X → ℝ) (c t : ℝ) : X → ℝ :=
  fun x => H x - 2 * c * Real.cos t ^ 2 * V x

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianCurveMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiating the finite Gaussian interpolation while removing the
nonuniform cavity penalty. The derivative is nonnegative under the
pointwise covariance-error bound. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {X : Type*} [Fintype X]

def cavityGaussianCurveMean {d : ℕ} (w H V : X → ℝ) (c : ℝ)
    (C A : X → Fin d → ℝ) (t : ℝ) : ℝ :=
  ∫ g, Real.log (finitePartition w (fun x => cavityPenaltyCurve H V c t x +
    linearGaussian (cavityGaussianCurve C A t) g x))
      ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1)

def cavityGaussianCurveSlope {d : ℕ} (w H V : X → ℝ) (c : ℝ)
    (C A : X → Fin d → ℝ) (t : ℝ) : ℝ :=
  ∫ g, ∑ x, gaussianGibbs w (cavityPenaltyCurve H V c t) (cavityGaussianCurve C A t) g x *
    (4 * c * Real.sin t * Real.cos t * V x + linearGaussian (cavityGaussianCurveDerivative C A t) g x)
      ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityReplicaCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit normalization of a cutoff in a bounded two-replica test.
The ratio convention also covers an empty cutoff. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Classical

namespace InvariantIsing

def cavityCutoffReplicaMean {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (H : X → ℝ) (s : Set X) (F : (Fin 2 → X) → ℝ) : ℝ :=
  referenceReplicaMean ν H (fun σ => if ∀ i, σ i ∈ s then F σ else 0) /
    referenceReplicaMean ν H (fun σ : Fin 2 → X => if ∀ i, σ i ∈ s then 1 else 0)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityReplicaSecant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Expected bounded replica tests are controlled by the corresponding
Gaussian log partitions, with a uniform quadratic secant error. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def cavityCylinderLogPartition {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (H : X → ℝ) (A : X → ℕ →₀ ℝ) : ℝ :=
  ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν)
    ∂gaussianCoordinates

def cavityCylinderReplicaMean {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (H : X → ℝ) (A : X → ℕ →₀ ℝ) {r : ℕ} (F : (Fin r → X) → ℝ) : ℝ :=
  ∫ g : ℕ → ℝ, referenceReplicaMean ν (fun x => H x + cylinderField (A x) g) F
    ∂gaussianCoordinates

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectorCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Projector coordinates give the same Gaussian covariance as the
eigenbasis coordinates, without choosing an eigenbasis measurably. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

def cavitySpectralProjector {N : ℕ} (V : Orthogonal N) (I : Finset (Fin N)) :
    Matrix (Fin N) (Fin N) ℝ :=
  cavityConjugate V (Matrix.diagonal (fun i => if i∈I then (1:ℝ) else 0))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRootedResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quadratic cavity kernel with the common root retained in its state. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal RealInnerProductSpace

namespace InvariantIsing

def rootedResidualPrior {d : ℕ} (n : ℕ) (R : Matrix (Fin d) (Fin d) ℝ) :
    Kernel (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n)
      (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d)) :=
  ((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n).comap Prod.snd measurable_snd) ×ₖ
    Kernel.const (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n)
      (multivariateGaussian 0 R)

instance rootedResidualPrior_markov {d : ℕ} (n : ℕ)
    (R : Matrix (Fin d) (Fin d) ℝ) : IsMarkovKernel (rootedResidualPrior n R) := by
  unfold rootedResidualPrior
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def rootedResidualWeight {d : ℕ} (n : ℕ) (K : Matrix (Fin d) (Fin d) ℝ)
    (p : (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) ×
      (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (⟪cavityLeafSum n p.1.1 p.2.1 + p.2.2,
    Matrix.toEuclideanCLM (𝕜 := ℝ) K (cavityLeafSum n p.1.1 p.2.1 + p.2.2)⟫ / 2))

lemma measurable_rootedResidualWeight {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) : Measurable (rootedResidualWeight n K) := by
  have hY : Measurable (fun p : (EuclideanSpace ℝ (Fin d) ×
      NoiseTree (EuclideanSpace ℝ (Fin d)) n) ×
      (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d)) =>
      cavityLeafSum n p.1.1 p.2.1 + p.2.2) :=
    ((measurable_cavityLeafSum_joint n).comp
      (measurable_fst.fst.prodMk measurable_snd.fst)).add measurable_snd.snd
  exact ENNReal.measurable_ofReal.comp
    ((hY.inner ((Matrix.toEuclideanCLM (𝕜 := ℝ) K).measurable.comp hY)).div_const 2).exp

lemma measurable_cavityQuadraticResidualGibbs_joint {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) :
    Measurable (fun p : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n =>
      cavityQuadraticResidualGibbs n K R p.1 p.2) := by
  have hm := measurable_normalizeMass.comp (measurable_random_withDensity
    (ν := rootedResidualPrior n R) (W := rootedResidualWeight n K)
    (rootedResidualPrior n R).measurable (measurable_rootedResidualWeight n K))
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  unfold cavityQuadraticResidualGibbs rootedResidualWeight
  dsimp only [Function.comp_def]
  rw [rootedResidualPrior, Kernel.prod_apply, Kernel.comap_apply, Kernel.const_apply]

def cavityRootedResidualBaseKernel {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) :
    Kernel (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n)
      (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d)) :=
  ⟨fun p => cavityQuadraticResidualGibbs n K R p.1 p.2,
    measurable_cavityQuadraticResidualGibbs_joint n K R⟩

instance cavityRootedResidualBaseKernel_markov {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) :
    IsMarkovKernel (cavityRootedResidualBaseKernel n K R) := by
  constructor
  intro p
  change IsProbabilityMeasure (cavityQuadraticResidualGibbs n K R p.1 p.2)
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def cavityRootedResidualKernel {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) :
    Kernel (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n)
      (EuclideanSpace ℝ (Fin d) ×
        (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) :=
  Kernel.deterministic Prod.fst measurable_fst ×ₖ cavityRootedResidualBaseKernel n K R

instance cavityRootedResidualKernel_markov {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) :
    IsMarkovKernel (cavityRootedResidualKernel n K R) := by
  unfold cavityRootedResidualKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def cavityRootedField {d : ℕ} (n : ℕ)
    (x : EuclideanSpace ℝ (Fin d) ×
      (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) :
    EuclideanSpace ℝ (Fin d) := cavityLeafSum n x.1 x.2.1 + x.2.2

lemma measurable_cavityRootedField {d : ℕ} (n : ℕ) :
    Measurable (cavityRootedField (d := d) n) :=
  ((measurable_cavityLeafSum_joint n).comp
    (measurable_fst.prodMk measurable_snd.fst)).add measurable_snd.snd

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFullTilt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identifying the two successive tilts with the full cavity factor on
the original leaf/residual/spin prior, with the common root retained. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal RealInnerProductSpace Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

def cavityRootedPriorKernel {d : ℕ} (n : ℕ) (R : Matrix (Fin d) (Fin d) ℝ) :
    Kernel (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n)
      (EuclideanSpace ℝ (Fin d) ×
        (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) :=
  Kernel.deterministic Prod.fst measurable_fst ×ₖ
    (((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n).comap Prod.snd measurable_snd) ×ₖ
      Kernel.const _ (multivariateGaussian 0 R))

instance cavityRootedPriorKernel_markov {d : ℕ} (n : ℕ)
    (R : Matrix (Fin d) (Fin d) ℝ) : IsMarkovKernel (cavityRootedPriorKernel n R) := by
  unfold cavityRootedPriorKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def cavityRootedQuadratic {d : ℕ} (n : ℕ) (K : Matrix (Fin d) (Fin d) ℝ)
    (x : EuclideanSpace ℝ (Fin d) ×
      (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) : ℝ :=
  ⟪cavityRootedField n x, Matrix.toEuclideanCLM (𝕜 := ℝ) K (cavityRootedField n x)⟫ / 2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOverlapError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-rank overlap errors in cavity coordinates. The retained
coordinates cancel exactly; the error is controlled by the special
projections and the fixed number of added spins. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def cavityCoordinatePairing {d : ℕ} (U : Rotation d) (I : Finset (Fin d))
    (x y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i ∈ I, U x i * U y i

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBaseOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single physical base eigenframe identifies every retained group
overlap with the corresponding projected spin overlap. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

def cavityBaseGroup {N m d : ℕ} (k : Fin m → ℕ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (a₀ : Fin d → Fin m) (a : Fin m) : Finset (Fin N) :=
  Finset.univ.filter (fun j => Sum.elim (fun v => v.1) a₀ (e.symm j) = a)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGroupedCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selected columns in spectral groups and their exact spin coordinates.
These are the vectors to which the fresh-frame Gaussian limit applies. -/

noncomputable section
open MeasureTheory
open scoped Matrix BigOperators

namespace InvariantIsing

def cavityGroupedSelectedFrame {N m q d : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (f : Fin d → Fin m × Fin q)
    (A : (a : Fin m) → Matrix (Fin (k a)) (Fin q) ℝ) : Matrix (Fin N) (Fin d) ℝ :=
  fun i j => (cavityGroupFrame k e (f j).1 * A (f j).1) i (f j).2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySelectedGroupFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Completion of the selected canonical axes to a fixed orthonormal
frame in each spectral group. Only finitely many cavity axes are added. -/

noncomputable section
open scoped Matrix BigOperators

namespace InvariantIsing

def cavityGroupIndexEquiv {N m : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (a : Fin m) :
    Fin (k a) ≃ {i : Fin N // (e.symm i).1=a} :=
  (Equiv.sigmaSubtype a).symm.trans
    (e.subtypeEquivOfSubtype' (p := fun w => w.1=a))

lemma cavityGroupIndexEquiv_apply {N m : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (a : Fin m) (j : Fin (k a)) :
    ((cavityGroupIndexEquiv k e a) j).val = e ⟨a,j⟩ := rfl

lemma cavity_group_selected_embedding {N m d : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (s : Fin d → Fin N) (hs : Function.Injective s) (g : Fin d → Fin m)
    (hg : ∀ j, (e.symm (s j)).1=g j) (hk : ∀ a, d ≤ k a) :
    ∃ f : (a : Fin m) → Fin d ↪ Fin (k a), ∀ j, e ⟨g j,f (g j) j⟩=s j := by
  classical
  let b (a : Fin m) : Fin d ↪ Fin (k a) := ⟨fun j => j.castLE (hk a), Fin.castLE_injective _⟩
  let t (a : Fin m) : {j : Fin d // g j=a} → Fin (k a) := fun j =>
    (cavityGroupIndexEquiv k e a).symm ⟨s j.1, (hg j.1).trans j.2⟩
  have ht a : Function.Injective (t a) := by
    intro i j hij
    apply Subtype.ext
    apply hs
    have hh := congrArg (fun z => ((cavityGroupIndexEquiv k e a) z).val) hij
    simpa only [t, Equiv.apply_symm_apply] using hh
  have hb a : Function.Injective (fun j : {j : Fin d // g j=a} => b a j.1) :=
    (b a).injective.comp Subtype.val_injective
  choose P hP using fun a => Equiv.Perm.exists_extending_pair
    (fun j : {j : Fin d // g j=a} => b a j.1) (t a) (hb a) (ht a)
  refine ⟨fun a => (b a).trans (P a).toEmbedding, ?_⟩
  intro j
  have h := hP (g j) ⟨j,rfl⟩
  have he := congrArg (fun z => ((cavityGroupIndexEquiv k e (g j)) z).val) h
  simpa only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    cavityGroupIndexEquiv_apply, t, Equiv.apply_symm_apply] using he

def cavitySelectedGroupFrame {m d : ℕ} (k : Fin m → ℕ)
    (f : (a : Fin m) → Fin d ↪ Fin (k a)) (a : Fin m) :
    Matrix (Fin (k a)) (Fin d) ℝ := fun i j => if i=f a j then 1 else 0

lemma cavitySelectedGroupFrame_gram {m d : ℕ} (k : Fin m → ℕ)
    (f : (a : Fin m) → Fin d ↪ Fin (k a)) (a : Fin m) :
    (cavitySelectedGroupFrame k f a).transpose*cavitySelectedGroupFrame k f a=1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, cavitySelectedGroupFrame,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true,
    (f a).injective.eq_iff, Matrix.one_apply]

lemma cavitySelectedGroupFrame_columns {N m d : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (g : Fin d → Fin m) (f : (a : Fin m) → Fin d ↪ Fin (k a)) :
    cavityGroupedSelectedFrame k e (fun j => (g j,j)) (cavitySelectedGroupFrame k f) =
      fun i j => if i=e ⟨g j,f (g j) j⟩ then 1 else 0 := by
  ext i j
  simp only [cavityGroupedSelectedFrame, Matrix.mul_apply, cavityGroupFrame,
    cavitySelectedGroupFrame]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBaseGroups
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Grouping retained and exceptional base axes by the same spectral
labels. Their dimensions are the retained counts plus the finite extras. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

def cavityBaseGroupSumEquiv {m d : ℕ} (k : Fin m → ℕ) (g : Fin d → Fin m) :
    ((a : Fin m) × (Fin (k a) ⊕ {j : Fin d // g j=a})) ≃
      (((a : Fin m) × Fin (k a)) ⊕ Fin d) where
  toFun x := match x with
    | ⟨a,Sum.inl i⟩ => Sum.inl ⟨a,i⟩
    | ⟨_,Sum.inr j⟩ => Sum.inr j.1
  invFun x := match x with
    | Sum.inl ⟨a,i⟩ => ⟨a,Sum.inl i⟩
    | Sum.inr j => ⟨g j,Sum.inr ⟨j,rfl⟩⟩
  left_inv x := by
    rcases x with ⟨a,i | ⟨j,hj⟩⟩
    · rfl
    · cases hj
      rfl
  right_inv x := by
    rcases x with ⟨a,i⟩ | j <;> rfl

lemma cavityBaseGroupSumEquiv_label {m d : ℕ} (k : Fin m → ℕ) (g : Fin d → Fin m)
    (x : (a : Fin m) × (Fin (k a) ⊕ {j : Fin d // g j=a})) :
    Sum.elim (fun w => w.1) g (cavityBaseGroupSumEquiv k g x)=x.1 := by
  rcases x with ⟨a,i | j⟩
  · rfl
  · exact j.2

def cavityBaseGroupDimension {m d : ℕ} (k : Fin m → ℕ) (g : Fin d → Fin m)
    (a : Fin m) : ℕ := k a+Fintype.card {j : Fin d // g j=a}

def cavityBaseGroupEquiv {N m d : ℕ} (k : Fin m → ℕ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N) (g : Fin d → Fin m) :
    ((a : Fin m) × Fin (cavityBaseGroupDimension k g a)) ≃ Fin N :=
  (Equiv.sigmaCongrRight (fun a => finSumFinEquiv.symm.trans
    (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin {j : Fin d // g j=a}).symm))).trans
      ((cavityBaseGroupSumEquiv k g).trans e)

lemma cavityBaseGroupEquiv_label {N m d : ℕ} (k : Fin m → ℕ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N) (g : Fin d → Fin m)
    (i : Fin N) :
    ((cavityBaseGroupEquiv k e g).symm i).1 = Sum.elim (fun w => w.1) g (e.symm i) := by
  let E := cavityBaseGroupEquiv k e g
  have h (x : (a : Fin m) × Fin (cavityBaseGroupDimension k g a)) :
      Sum.elim (fun w => w.1) g (e.symm (E x))=x.1 := by
    change Sum.elim (fun w => w.1) g (e.symm (e (cavityBaseGroupSumEquiv k g _)))=x.1
    rw [e.symm_apply_apply, cavityBaseGroupSumEquiv_label]
    rfl
  simpa only [E, Equiv.apply_symm_apply] using (h (E.symm i)).symm

lemma cavityBaseGroupDimension_ge {m d : ℕ} (k : Fin m → ℕ) (g : Fin d → Fin m)
    (a : Fin m) : k a ≤ cavityBaseGroupDimension k g a := Nat.le_add_right _ _

theorem cavity_canonical_group_frames {N m d : ℕ} (k : Fin m → ℕ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N) (g : Fin d → Fin m)
    (hk : ∀ a, d ≤ k a) :
    ∃ A : (a : Fin m) → Matrix (Fin (cavityBaseGroupDimension k g a)) (Fin d) ℝ,
      (∀ a, (A a).transpose*A a=1) ∧
      cavityGroupedSelectedFrame (cavityBaseGroupDimension k g) (cavityBaseGroupEquiv k e g)
        (fun j => (g j,j)) A = cavityCanonicalSpecial e := by
  have hlabel j : ((cavityBaseGroupEquiv k e g).symm (e (Sum.inr j))).1=g j := by
    rw [cavityBaseGroupEquiv_label, e.symm_apply_apply]
    rfl
  obtain ⟨f,hf⟩ := cavity_group_selected_embedding (cavityBaseGroupDimension k g)
    (cavityBaseGroupEquiv k e g) (fun j => e (Sum.inr j))
    (e.injective.comp Sum.inr_injective) g hlabel
    (fun a => (hk a).trans (cavityBaseGroupDimension_ge k g a))
  refine ⟨cavitySelectedGroupFrame (cavityBaseGroupDimension k g) f,
    cavitySelectedGroupFrame_gram _ f, ?_⟩
  rw [cavitySelectedGroupFrame_columns]
  ext i j
  rw [hf]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGroupedGram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The vectors used by the fresh group frames have exactly the
physical projected-overlap covariance divided by the group density. -/

noncomputable section
open IsingPerceptron
open scoped Matrix

namespace InvariantIsing

def cavityGroupSetEquiv {N m : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (a : Fin m) :
    Fin (k a) ≃ ↥(cavitySpectralGroup (fun i => (e.symm i).1) a) :=
  (cavityGroupIndexEquiv k e a).trans (Equiv.subtypeEquivRight (by
    intro i
    simp only [cavitySpectralGroup, Finset.mem_filter, Finset.mem_univ, true_and]))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOrderedGroups
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical ordered finite spectral groups are literal contiguous windows.
This fixes the full/base spectral ordering in the rational cavity sequence. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def cavityOrderedStart {m : ℕ} (dims : Fin m → ℕ) (a : Fin m) : ℕ :=
  ∑ i : Fin a, dims (Fin.castLE a.isLt.le i)

def cavityOrderedEquiv {N m : ℕ} (dims : Fin m → ℕ) (hsum : ∑ a, dims a=N) :
    ((a : Fin m) × Fin (dims a)) ≃ Fin N :=
  finSigmaFinEquiv.trans (finCongr hsum)

def cavityOrderedGroup {N m : ℕ} (dims : Fin m → ℕ) (hsum : ∑ a, dims a=N)
    (i : Fin N) : Fin m := ((cavityOrderedEquiv dims hsum).symm i).1

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOrderedBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The retained and special axes can be identified with the same ordered
spectral basis used for the scalar pressure sequence. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def cavityOrderedBase {N m d : ℕ} (k : Fin m → ℕ) (g : Fin d → Fin m)
    (hsum : ∑ a, cavityBaseGroupDimension k g a=N) :
    (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N :=
  let e := Fintype.equivFin (((a : Fin m) × Fin (k a)) ⊕ Fin d)
  e.trans ((cavityBaseGroupEquiv k e g).symm.trans
    (cavityOrderedEquiv (cavityBaseGroupDimension k g) hsum))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRationalCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A rational spectral law gives an exact arithmetic progression of
positive multiplicities and the finite exceptional-axis multiplicities. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def cavityRationalCount {m : ℕ} (s : Fin m → ℕ) (q r : ℕ) (a : Fin m) : ℕ :=
  (r+q)*s a

lemma cavityRationalCount_sum {m n : ℕ} (s : Fin m → ℕ) (hs : ∑ a, s a=n)
    (q r : ℕ) : ∑ a, cavityRationalCount s q r a=(r+q)*n := by
  simp only [cavityRationalCount, ← Finset.mul_sum, hs]

lemma cavityRationalCount_step {m : ℕ} (s : Fin m → ℕ) (q r : ℕ) (a : Fin m) :
    cavityRationalCount s q (r+1) a=cavityRationalCount s q r a+s a := by
  unfold cavityRationalCount
  ring

lemma cavityRationalCount_le_total {m n : ℕ} (s : Fin m → ℕ) (hs : ∑ a, s a=n)
    (a : Fin m) : s a≤n := by
  rw [← hs]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

lemma cavityRationalRetained_base {m n d : ℕ} (s : Fin m → ℕ) (hs : ∀ a, 0 < s a)
    (hsum : ∑ a, s a=n) (r : ℕ) (a : Fin m) :
    (cavityRationalCount s (d+n+3) (r+1) a-n)+(n-s a)=
      cavityRationalCount s (d+n+3) r a := by
  have hsn := cavityRationalCount_le_total s hsum a
  have hp := Nat.le_mul_of_pos_right (r+1+(d+n+3)) (hs a)
  rw [cavityRationalCount_step]
  have hbase : n ≤ cavityRationalCount s (d+n+3) r a := by
    unfold cavityRationalCount
    have h := Nat.le_mul_of_pos_right (r+(d+n+3)) (hs a)
    omega
  omega

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRationalBaseCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The special axes have exactly the missing rational multiplicities,
so the retained-plus-special base spectrum equals the prescribed count. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma cavityBaseGroupDimension_filter_card {m d : ℕ} (k : Fin m → ℕ)
    (g : Fin d → Fin m) (a : Fin m) :
    cavityBaseGroupDimension k g a=k a+(Finset.univ.filter (fun j => g j=a)).card := by
  simp only [cavityBaseGroupDimension, Fintype.card_subtype]

lemma cavityRationalBase_counts {m n d : ℕ} (s : Fin m → ℕ) (hs : ∀ a, 0 < s a)
    (hsum : ∑ a, s a=n) (g : Fin d → Fin m)
    (hg : ∀ a, (Finset.univ.filter (fun j => g j=a)).card=n-s a) (r : ℕ) (a : Fin m) :
    cavityBaseGroupDimension (fun a => cavityRationalCount s (d+n+3) (r+1) a-n) g a=
      cavityRationalCount s (d+n+3) r a := by
  rw [cavityBaseGroupDimension_filter_card, hg]
  exact cavityRationalRetained_base s hs hsum r a

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRationalWindows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact contiguous full-system windows for a rational spectral law. -/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace InvariantIsing

lemma cavityRationalMass_positive {m n : ℕ} (s : Fin m → ℕ) (hs : ∀ a, 0 < s a)
    (hn : 0<n) (a : Fin m) : 0<(s a : ℝ)/n :=
  div_pos (by exact_mod_cast hs a) (by exact_mod_cast hn)

lemma cavityRationalMass_sum {m n : ℕ} (s : Fin m → ℕ) (hs : ∑ a, s a=n) (hn : 0<n) :
    ∑ a, (s a : ℝ)/n=1 := by
  rw [← Finset.sum_div, ← Nat.cast_sum, hs, div_self (Nat.cast_ne_zero.mpr hn.ne')]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRationalRetained
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact finite group equivalences in the rational cavity coupling. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def cavityRationalSize (n d r : ℕ) : ℕ := (r+(d+n+3))*n

def cavityRationalRetained {m : ℕ} (n d : ℕ) (s : Fin m → ℕ) (r : ℕ) (a : Fin m) : ℕ :=
  cavityRationalCount s (d+n+3) (r+1) a-n

lemma cavityRationalSize_ge_three (n d r : ℕ) (hn : 0 < n) :
    3 ≤ cavityRationalSize n d r := by
  have hh := Nat.le_mul_of_pos_right (r+(d+n+3)) hn
  unfold cavityRationalSize
  omega

lemma cavityRationalRetained_full {m n : ℕ} (s : Fin m → ℕ) (hs : ∀ a, 0 < s a)
    (d r : ℕ) (a : Fin m) :
    cavityRationalRetained n d s r a+n=cavityRationalCount s (d+n+3) (r+1) a := by
  unfold cavityRationalRetained
  apply Nat.sub_add_cancel
  have hh := Nat.le_mul_of_pos_right (r+1+(d+n+3)) (hs a)
  unfold cavityRationalCount
  omega

lemma cavityRationalBase_dimension {m n d : ℕ} (s : Fin m → ℕ) (hs : ∀ a, 0 < s a)
    (hsum : ∑ a, s a=n) (g : Fin d → Fin m)
    (hg : ∀ a, (Finset.univ.filter (fun j => g j=a)).card=n-s a) (r : ℕ) (a : Fin m) :
    cavityBaseGroupDimension (cavityRationalRetained n d s r) g a=
      cavityRationalCount s (d+n+3) r a :=
  cavityRationalBase_counts s hs hsum g hg r a

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityAffineCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed integer offsets in the block counts cover every residue class
of physical dimensions without changing the limiting rational masses. -/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace InvariantIsing

def cavityAffineCount {m : ℕ} (s c : Fin m → ℕ) (q r : ℕ) (a : Fin m) : ℕ :=
  cavityRationalCount s q r a+c a

def cavityAffineSize {m : ℕ} (n q : ℕ) (c : Fin m → ℕ) (r : ℕ) : ℕ :=
  (r+q)*n+∑ a, c a

lemma cavityAffineCount_sum {m n : ℕ} (s c : Fin m → ℕ) (hsum : ∑ a, s a=n)
    (q r : ℕ) : ∑ a, cavityAffineCount s c q r a=cavityAffineSize n q c r := by
  simp only [cavityAffineCount, Finset.sum_add_distrib, cavityRationalCount_sum s hsum,
    cavityAffineSize]

lemma cavityAffineSize_ge_three {m : ℕ} (n d : ℕ) (c : Fin m → ℕ)
    (r : ℕ) (hn : 0 < n) : 3 ≤ cavityAffineSize n (d+n+3) c r :=
  (cavityRationalSize_ge_three n d r hn).trans (Nat.le_add_right _ _)

lemma cavityAffineSize_succ {m : ℕ} (n q : ℕ) (c : Fin m → ℕ) (r : ℕ) :
    cavityAffineSize n q c (r+1)=cavityAffineSize n q c r+n := by
  dsimp only [cavityAffineSize]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityAffineRetained
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The retained and special axes for counts with a fixed residue offset. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def cavityAffineRetained {m : ℕ} (n d : ℕ) (s c : Fin m → ℕ) (r : ℕ) (a : Fin m) : ℕ :=
  cavityRationalRetained n d s r a+c a

lemma cavityAffineRetained_full {m n : ℕ} (s c : Fin m → ℕ) (hs : ∀ a, 0 < s a)
    (d r : ℕ) (a : Fin m) :
    cavityAffineRetained n d s c r a+n=cavityAffineCount s c (d+n+3) (r+1) a := by
  dsimp only [cavityAffineRetained, cavityAffineCount]
  rw [Nat.add_right_comm, cavityRationalRetained_full s hs]

lemma cavityAffineFull_sum {m n : ℕ} (s c : Fin m → ℕ) (hsum : ∑ a, s a=n)
    (q r : ℕ) : ∑ a, cavityAffineCount s c q (r+1) a=cavityAffineSize n q c r+n := by
  rw [cavityAffineCount_sum s c hsum, cavityAffineSize_succ]

def cavityAffineFullGroup {m n : ℕ} (s c : Fin m → ℕ) (hsum : ∑ a, s a=n)
    (d r : ℕ) : Fin (cavityAffineSize n (d+n+3) c r+n) → Fin m :=
  cavityOrderedGroup (cavityAffineCount s c (d+n+3) (r+1))
    (cavityAffineFull_sum s c hsum (d+n+3) r)

def cavityAffineRetainedEquiv {m n : ℕ} (s c : Fin m → ℕ) (hs : ∀ a, 0 < s a)
    (hsum : ∑ a, s a=n) (d r : ℕ) (a : Fin m) :
    {i : Fin (cavityAffineSize n (d+n+3) c r+n) // cavityAffineFullGroup s c hsum d r i=a} ≃
      Fin (cavityAffineRetained n d s c r a+n) :=
  (cavityGroupIndexEquiv (cavityAffineCount s c (d+n+3) (r+1))
    (cavityOrderedEquiv _ (cavityAffineFull_sum s c hsum (d+n+3) r)) a).symm.trans
      (finCongr (cavityAffineRetained_full s c hs d r a).symm)

lemma cavityAffineBase_dimension {m n d : ℕ} (s c : Fin m → ℕ) (hs : ∀ a, 0 < s a)
    (hsum : ∑ a, s a=n) (g : Fin d → Fin m)
    (hg : ∀ a, (Finset.univ.filter (fun j => g j=a)).card=n-s a) (r : ℕ) (a : Fin m) :
    cavityBaseGroupDimension (cavityAffineRetained n d s c r) g a=
      cavityAffineCount s c (d+n+3) r a := by
  have hh := cavityRationalBase_dimension s hs hsum g hg r a
  simp only [cavityBaseGroupDimension_filter_card] at hh ⊢
  dsimp only [cavityAffineRetained, cavityAffineCount]
  rw [Nat.add_right_comm, hh]

lemma cavityAffineBase_sum {m n d : ℕ} (s c : Fin m → ℕ) (hs : ∀ a, 0 < s a)
    (hsum : ∑ a, s a=n) (g : Fin d → Fin m)
    (hg : ∀ a, (Finset.univ.filter (fun j => g j=a)).card=n-s a) (r : ℕ) :
    ∑ a, cavityBaseGroupDimension (cavityAffineRetained n d s c r) g a=
      cavityAffineSize n (d+n+3) c r := by
  simp_rw [cavityAffineBase_dimension s c hs hsum g hg r]
  exact cavityAffineCount_sum s c hsum (d+n+3) r

def cavityAffineBaseEquiv {m n d : ℕ} (s c : Fin m → ℕ) (hs : ∀ a, 0 < s a)
    (hsum : ∑ a, s a=n) (g : Fin d → Fin m)
    (hg : ∀ a, (Finset.univ.filter (fun j => g j=a)).card=n-s a) (r : ℕ) :
    (((a : Fin m) × Fin (cavityAffineRetained n d s c r a)) ⊕ Fin d) ≃
      Fin (cavityAffineSize n (d+n+3) c r) :=
  cavityOrderedBase (cavityAffineRetained n d s c r) g (cavityAffineBase_sum s c hs hsum g hg r)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityAffineFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One spectrum on all sizes for each fixed vector of residue offsets. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def cavityAffineLabel {m n : ℕ} (hm : 0 < m) (s c : Fin m → ℕ)
    (hsum : ∑ a, s a=n) (N : ℕ) : Fin N → Fin m :=
  if h : (∑ a, c a) ≤ N ∧ n∣(N-∑ a, c a) then
    cavityOrderedGroup (fun a => (N-∑ a, c a)/n*s a+c a) (by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum,
        Nat.div_mul_cancel h.2, Nat.sub_add_cancel h.1])
  else fun _ => ⟨0,hm⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityStrictLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict overlap levels for the finite-cascade approximation.  A small
convex mixture with evenly spaced interior levels removes ties and the
unit top endpoint while moving every level by at most the mixture size. -/

noncomputable section
open Set

namespace InvariantIsing

def cavityInteriorLevel {n : ℕ} (i : Fin (n + 1)) : ℝ :=
  ((i : ℕ) + 1 : ℝ) / (n + 2 : ℕ)

lemma cavityInteriorLevel_mem {n : ℕ} (i : Fin (n + 1)) :
    cavityInteriorLevel i ∈ Ioo (0 : ℝ) 1 := by
  have hd : (0 : ℝ) < (n + 2 : ℕ) := by positivity
  have hi : ((i : ℕ) + 1 : ℝ) < (n + 2 : ℕ) := by
    exact_mod_cast (show i.val + 1 < n + 2 by omega)
  exact ⟨div_pos (by positivity) hd, (div_lt_one hd).mpr hi⟩

lemma cavityInteriorLevel_strict (n : ℕ) :
    StrictMono (cavityInteriorLevel (n := n)) := by
  intro i j hij
  apply (div_lt_div_iff_of_pos_right (show (0 : ℝ) < (n + 2 : ℕ) by positivity)).mpr
  simpa only [add_comm] using add_lt_add_right (Nat.cast_lt.mpr hij : (i.val : ℝ) < j.val) 1

def cavityStrictLevels {n : ℕ} (q : Fin (n + 1) → ℝ) (ε : ℝ)
    (i : Fin (n + 1)) : ℝ := (1 - ε) * q i + ε * cavityInteriorLevel i

lemma cavityStrictLevels_mem {n : ℕ} (q : Fin (n + 1) → ℝ)
    (hq : ∀ i, q i ∈ Icc (0 : ℝ) 1) {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) 1)
    (i : Fin (n + 1)) : cavityStrictLevels q ε i ∈ Ioo (0 : ℝ) 1 := by
  have hi := cavityInteriorLevel_mem i
  have hq' := hq i
  have hnon : 0 ≤ (1 - ε) * q i := mul_nonneg (sub_nonneg.mpr hε.2) hq'.1
  have hpos : 0 < ε * cavityInteriorLevel i := mul_pos hε.1 hi.1
  have hlo : (1 - ε) * q i ≤ (1 - ε) := by nlinarith [mul_nonneg (sub_nonneg.mpr hε.2) (sub_nonneg.mpr hq'.2)]
  have hhi : ε * cavityInteriorLevel i < ε := by nlinarith [mul_pos hε.1 (sub_pos.mpr hi.2)]
  constructor <;> dsimp only [cavityStrictLevels] <;> linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityStrictUniformPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform finite overlap paths with strictly increasing interior
levels. Their endpoint convention is fixed, and they converge to the
original quantile almost everywhere and in L1. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped Topology

namespace InvariantIsing

def cavityUniformLevel (n : ℕ) (s : ℝ) : Fin (n + 1) :=
  ⟨uniformCellIndex n s, Nat.lt_succ_of_le (uniformCellIndex_le n s)⟩

lemma cavityUniformLevel_monotone (n : ℕ) : Monotone (cavityUniformLevel n) := by
  intro s t hst
  change min n ⌊(n + 1 : ℕ) * s⌋₊ ≤ min n ⌊(n + 1 : ℕ) * t⌋₊
  exact min_le_min_left n (Nat.floor_mono
    (mul_le_mul_of_nonneg_left hst (by positivity)))

lemma cavity_uniform_epsilon (n : ℕ) : (1 / ((n : ℝ) + 1)) ∈ Ioc (0 : ℝ) 1 := by
  constructor
  · positivity
  · apply (div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySampledBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral arrays and finite blocks sampled from the same original
Gibbs configurations, with their disorder retained. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def cavitySampledEntryArray {m : ℕ} {Ω X : Type*}
    (B : Ω → X → X → SpectralEntry (m + 1)) (p : Ω × (ℕ → X)) :
    SpectralArray (m + 1) := fun ij => B p.1 (p.2 ij.1) (p.2 ij.2)

def cavitySampledGroupBlock {m r : ℕ} {Ω X : Type*}
    (B : Ω → X → X → SpectralEntry (m + 1)) (ω : Ω) (σ : Fin r → X) :
    SpectralBlock m r := fun i j a => B ω (σ i) (σ j) a.castSucc

lemma measurable_cavitySampledEntryArray {m : ℕ} {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (B : Ω → X → X → SpectralEntry (m + 1))
    (hB : ∀ x y, Measurable (fun ω => B ω x y)) :
    Measurable (cavitySampledEntryArray B) := by
  have hb : Measurable (fun p : Ω × (X × X) => B p.1 p.2.1 p.2.2) := by
    apply measurable_from_prod_countable_left
    intro xy
    exact hB xy.1 xy.2
  apply Measurable.of_eval
  intro ij
  have hp : Measurable (fun p : Ω × (ℕ → X) => (p.1, (p.2 ij.1, p.2 ij.2))) := by fun_prop
  exact hb.comp hp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBaseAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-volume perturbation minimizers provide exactly the natural-index
amplitudes used in the physical cavity model. The unused coordinates are one. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def cavityBaseAmplitude {N : ℕ} (u : Fin N → ℝ) (j : ℕ) : ℝ :=
  if hj : j < N then u ⟨j,hj⟩ else 1

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBoundaryCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous upper and lower approximations to a hard radial cutoff. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace InvariantIsing

def cavityBoundaryUpper (r B x : ℝ) : ℝ := cavityRadialCutoff 0 (r*(x-B))
def cavityBoundaryLower (r B x : ℝ) : ℝ := cavityRadialCutoff 0 (r*(x-B)+1)
def cavityBoundaryGap (r B x : ℝ) : ℝ := cavityBoundaryUpper r B x-cavityBoundaryLower r B x

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCanonicalGroupAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual canonical cavity frame admits the fresh-group Gibbs
representation. No new independent-frame assumption is required. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

def cavityCanonicalGroupFrame {N m d : ℕ} (k : Fin m → ℕ)
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N) (g : Fin d → Fin m)
    (hk : ∀ a, d ≤ k a) :
    (a : Fin m) → Matrix (Fin (cavityBaseGroupDimension k g a)) (Fin d) ℝ :=
  Classical.choose (cavity_canonical_group_frames k e g hk)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCompressionLimitGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The limiting frame extracted from the concrete compression has the
orthogonality and completeness used in the finite spectral cavity model. -/

noncomputable section
open Filter
open scoped Matrix Topology

namespace InvariantIsing

def cavityCompressionLimitFrame {m n d : ℕ} (e : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) : Matrix (Fin (m*n)) (Fin d) ℝ :=
  fun i j => B₀ (e i) j

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySchurDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar derivative in `cav:determinant-derivative` after exact
finite multiplicity evaluation of the matrix determinant. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def cavitySpectralLogDet {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) (x : ℝ) : ℝ :=
  Real.log x + ∑ a, rho a * Real.log (finiteInverse rho lam hrho hsum x - lam a)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLogDetPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous zero-endpoint form of the scalar logarithmic determinant.
It retains the ordinary residual contribution, whose cascade exponent is one. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

def cavityLogDetPotential {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) (x : ℝ) : ℝ :=
  ∑ a, rho a * Real.log (1 + x * (finiteR rho lam hrho hsum x - lam a))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteNormalizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evaluation of the quadratic root/gap/residual normalizer on a finite
trial overlap path. No quadratic marking or limiting formula is assumed. -/

noncomputable section
open MeasureTheory Set
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology

namespace InvariantIsing

def cavityFiniteQuadraticMean {d l : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (H : Fin (l + 1) → Matrix (Fin d) (Fin d) ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (cut : Fin (l + 2) → ℝ) : ℝ :=
  Matrix.trace (S₀ * cavityBackwardQuadratic K (H 0)) / 2 -
    (∑ i : Fin l, Real.log ((1 - H i.castSucc * K).det / (1 - H i.succ * K).det) /
      (2 * cut i.castSucc.succ)) - Real.log (1 - H (Fin.last l) * K).det / 2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianMarkedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The joint law of an overlap label and its Gaussian cavity marks.
The covariance is allowed to be singular. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

variable {a L : Type*} [Fintype a] [DecidableEq a]
  [MetricSpace L] [MeasurableSpace L] [BorelSpace L]

def cavityGaussianMarkedMap
    (p : (L × Matrix a a ℝ) × EuclideanSpace ℝ a) : L × EuclideanSpace ℝ a :=
  (p.1.1, p.2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarMarkedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint probability laws for the physical fresh Haar marks. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

variable {m r q : ℕ} {N : Fin m → ℕ} {X L : Type*}
  [MeasurableSpace X] [MetricSpace L] [MeasurableSpace L]
  [BorelSpace L] [SecondCountableTopology L]

def cavityHaarMarkedMap (l : X → L)
    (v : X → (a : Fin m) → Fin r → Fin (N a) → ℝ)
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (p : X × ((a : Fin m) → Orthogonal (N a))) :
    L × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) :=
  (l p.1, cavityGroupMatrixProjection (v p.1) (cavityGroupHaarFrames A₀ p.2))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLinearSpinEvaluation
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evaluation of the full linear cavity spin test under its independent
Euclidean Gaussian forest and root. The covariance assumptions specify
the scalar field path after projection. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix NNReal

namespace InvariantIsing

def cavityLinearFieldCoordinateLaw {d : ℕ} (h : FieldStep)
    (S : ℕ → Matrix (Fin d) (Fin d) ℝ) :
    Measure (LabeledTree h.depth × (ForestVertex h.depth → EuclideanSpace ℝ (Fin d))) :=
  (labeledCascadeLaw h.depth (chainExponent h.cut) : Measure (LabeledTree h.depth)).prod
    (Measure.infinitePi (fun a : ForestVertex h.depth =>
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth h.depth a))))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLinearIntegrability
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full linear cavity exponential moment on almost every actual
independent Gaussian forest. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix NNReal

namespace InvariantIsing

instance cavityLinearFieldCoordinateLaw_isProbabilityMeasure {d : ℕ} (h : FieldStep)
    (S : ℕ → Matrix (Fin d) (Fin d) ℝ) :
    IsProbabilityMeasure (cavityLinearFieldCoordinateLaw h S) := by
  unfold cavityLinearFieldCoordinateLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityMarkedTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The usual weak topology, with the marked replica space specified
before synthesizing its measurable topology. -/

noncomputable section
open MeasureTheory

namespace InvariantIsing

instance cavityMarkedProbabilityTopology {m r q : ℕ} :
    TopologicalSpace (ProbabilityMeasure
      (SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)))) :=
  @ProbabilityMeasure.instTopologicalSpace
    (SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)))
    inferInstance inferInstance inferInstance

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOrientation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Correcting a spectral row sign sends an orthogonal matrix to SO
without changing its spectral compression blocks. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

def cavityOrientationSign {N : ℕ} (hN : 0 < N) (U : Orthogonal N) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (fun i => if i = (⟨0, hN⟩ : Fin N) then (U : Matrix (Fin N) (Fin N) ℝ).det else 1)

lemma cavityOrientationSign_square {N : ℕ} (hN : 0 < N) (U : Orthogonal N) :
    cavityOrientationSign hN U * (cavityOrientationSign hN U).transpose = 1 := by
  rw [cavityOrientationSign, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    split_ifs
    · rcases orthogonal_det_eq_one_or_neg_one U with h | h <;> rw [h] <;> norm_num
    · norm_num
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

lemma cavityOrientationSign_det {N : ℕ} (hN : 0 < N) (U : Orthogonal N) :
    (cavityOrientationSign hN U).det = (U : Matrix (Fin N) (Fin N) ℝ).det := by
  simp [cavityOrientationSign, Matrix.det_diagonal]

def cavityOrientationLift {N : ℕ} (hN : 0 < N) (U : Orthogonal N) : SpecialOrthogonal N :=
  ⟨cavityOrientationSign hN U * (U : Matrix (Fin N) (Fin N) ℝ), by
    apply Matrix.mem_specialOrthogonalGroup_iff.mpr
    constructor
    · apply (Matrix.mem_orthogonalGroup_iff (Fin N) ℝ).mpr
      rw [Matrix.transpose_mul]
      calc
        _ = cavityOrientationSign hN U *
            ((U : Matrix (Fin N) (Fin N) ℝ) * (U : Matrix (Fin N) (Fin N) ℝ).transpose) *
              (cavityOrientationSign hN U).transpose := by simp only [Matrix.mul_assoc]
        _ = 1 := by
          rw [(Matrix.mem_orthogonalGroup_iff (Fin N) ℝ).mp U.property]
          simpa only [Matrix.mul_one] using cavityOrientationSign_square hN U
    · rw [Matrix.det_mul, cavityOrientationSign_det]
      rcases orthogonal_det_eq_one_or_neg_one U with h | h <;> rw [h] <;> norm_num⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityReplicaRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The maximum selected-coordinate norm gives exactly the simultaneous
spatial restriction of every replica. A common divergent sequence of
radii avoids the boundaries of all the limiting replica laws. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

def cavityReplicaRadius {m r q d : ℕ} {L : Type*}
    (J : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin d)))
    (p : L × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))) : ℝ := ‖J p.2‖

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRootedSpinChange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full spin change of variables with the common Gaussian root retained. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

def cavitySpinDisorderInnovation {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (b : ℕ → ℝ) (ω : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H 0 * K)⁻¹ ω.1,
    cavityInnovationTree n b (cavityGaussianMarks S)
      (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
      (fun i => cavityStepInnovation K (H i) (H (i + 1))) ω.1 ω.2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityWeakRadialCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak convergence of a bounded continuous replica test restricted by
a continuous radius, at any radius with zero limiting boundary mass. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

def cavityBoundaryProfile {E : Type*} [TopologicalSpace E]
    (R : E → ℝ) (hR : Continuous R) (r B c : ℝ) : E →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => cavityRadialCutoff 0 (r*(R x-B)+c))
    ((continuous_cavityRadialCutoff 0).comp (by fun_prop)) 1 (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (cavityRadialCutoff_mem 0 _).1]
      exact (cavityRadialCutoff_mem 0 _).2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOverlapWeightedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded continuous extension of the overlap-weighted test from
[-1,1], for the full original-model self-consistency identity. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BoundedContinuousFunction

namespace InvariantIsing

def cavityOverlapWeightedTest (Φ : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => Φ x * (Set.projIcc (-1) 1 (by norm_num) x : ℝ))
    (Φ.continuous.mul (continuous_subtype_val.comp (continuous_projIcc (h := (by norm_num : (-1 : ℝ) ≤ 1))))) ‖Φ‖
    (fun x => by
      rw [Real.norm_eq_abs,abs_mul]
      have hx : |(Set.projIcc (-1) 1 (by norm_num) x : ℝ)| ≤ 1 :=
        abs_le.mpr (Set.projIcc (-1) 1 (by norm_num) x).property
      exact (mul_le_mul (by simpa only [Real.norm_eq_abs] using Φ.norm_coe_le_norm x)
        hx (abs_nonneg _) (norm_nonneg Φ)).trans_eq (mul_one _))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPrefixAffineFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One spectrum on all sizes for each fixed vector of residue offsets. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def cavityPrefixAffineSize {m : ℕ} (n q : ℕ) (c : Fin m → ℕ) (r : ℕ) : ℕ :=
  (∑ a, c a)+(r+q)*n

lemma cavityPrefixAffineCount_sum {m n : ℕ} (s c : Fin m → ℕ) (hsum : ∑ a, s a=n)
    (q r : ℕ) : ∑ a, cavityAffineCount s c q r a=cavityPrefixAffineSize n q c r := by
  simpa only [cavityAffineSize, cavityPrefixAffineSize, Nat.add_comm] using
    cavityAffineCount_sum s c hsum q r

lemma cavityPrefixAffineFull_sum {m n : ℕ} (s c : Fin m → ℕ) (hsum : ∑ a, s a=n)
    (q r : ℕ) : ∑ a, cavityAffineCount s c q (r+1) a=cavityPrefixAffineSize n q c r+n := by
  rw [cavityPrefixAffineCount_sum s c hsum]
  simp only [cavityPrefixAffineSize]
  ring

def cavityPrefixAffineFullGroup {m n : ℕ} (s c : Fin m → ℕ) (hsum : ∑ a, s a=n)
    (d r : ℕ) : Fin (cavityPrefixAffineSize n (d+n+3) c r+n) → Fin m :=
  cavityOrderedGroup (cavityAffineCount s c (d+n+3) (r+1))
    (cavityPrefixAffineFull_sum s c hsum (d+n+3) r)

def cavityPrefixAffineRetainedEquiv {m n : ℕ} (s c : Fin m → ℕ) (hs : ∀ a, 0 < s a)
    (hsum : ∑ a, s a=n) (d r : ℕ) (a : Fin m) :
    {i : Fin (cavityPrefixAffineSize n (d+n+3) c r+n) // cavityPrefixAffineFullGroup s c hsum d r i=a} ≃
      Fin (cavityAffineRetained n d s c r a+n) :=
  (cavityGroupIndexEquiv (cavityAffineCount s c (d+n+3) (r+1))
    (cavityOrderedEquiv _ (cavityPrefixAffineFull_sum s c hsum (d+n+3) r)) a).symm.trans
      (finCongr (cavityAffineRetained_full s c hs d r a).symm)

def cavityPrefixAffineBaseEquiv {m n d : ℕ} (s c : Fin m → ℕ) (hs : ∀ a, 0 < s a)
    (hsum : ∑ a, s a=n) (g : Fin d → Fin m)
    (hg : ∀ a, (Finset.univ.filter (fun j => g j=a)).card=n-s a) (r : ℕ) :
    (((a : Fin m) × Fin (cavityAffineRetained n d s c r a)) ⊕ Fin d) ≃
      Fin (cavityPrefixAffineSize n (d+n+3) c r) :=
  cavityOrderedBase (cavityAffineRetained n d s c r) g (by
    simpa only [cavityAffineSize, cavityPrefixAffineSize, Nat.add_comm] using
      cavityAffineBase_sum s c hs hsum g hg r)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityResidueFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical rational multiplicities at every physical dimension. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def cavityResidueOffset {m : ℕ} (hm : 0 < m) (t : ℕ) (a : Fin m) : ℕ :=
  if a=⟨0,hm⟩ then t else 0

def cavityResidueLabel {m n : ℕ} (hm : 0 < m) (s : Fin m → ℕ)
    (hsum : ∑ a, s a=n) (N : ℕ) : Fin N → Fin m :=
  cavityAffineLabel hm s (cavityResidueOffset hm (N%n)) hsum N

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityWindowInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two probabilistic compression premises follow from the actual
contiguous spectral windows and their positive limiting masses. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators

namespace InvariantIsing

def cavityCompressionGoodEvent {N n m : ℕ} (g : Fin (N+n) → Fin m) (L : ℝ) :
    Set (SpecialOrthogonal (N+n)) :=
  {U | ∀ a, ‖(CFC.sqrt (cavityCompressionGrams g (cavitySpecialOrthogonal U) a))⁻¹‖ ≤ L}

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_FiniteSpinEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite entropy and the log-sum variational bound used to project
canonical spins onto an attainable constrained block. Zero trial masses
are allowed and contribute zero. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def finiteCanonicalWeights {X : Type*} [Fintype X] (H : X → ℝ) (x : X) : ℝ :=
  Real.exp (H x) / ∑ y, Real.exp (H y)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedSpinLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricted spin sums retain the original cube mass. A deterministic
map of slices costs its energy error and the logarithm of its largest fiber. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def restrictedSpinLog {N : ℕ} (S : Finset (Spin N)) (H : Spin N → ℝ) : ℝ :=
  Real.log (∑ σ ∈ S, Real.exp (H σ)) - N * Real.log 2

lemma restrictedSpinLog_add_const {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (H : Spin N → ℝ) (c : ℝ) :
    restrictedSpinLog S (fun σ => H σ + c) = restrictedSpinLog S H + c := by
  have hp : 0 < ∑ σ ∈ S, Real.exp (H σ) :=
    Finset.sum_pos (fun σ _ => Real.exp_pos (H σ)) hS
  simp_rw [restrictedSpinLog, Real.exp_add]
  rw [← Finset.sum_mul, Real.log_mul hp.ne' (Real.exp_ne_zero c), Real.log_exp]
  ring

lemma restrictedSpinLog_mono {N : ℕ} {S T : Finset (Spin N)} (hS : S.Nonempty)
    (hST : S ⊆ T) {H K : Spin N → ℝ} (hHK : ∀ σ ∈ S, H σ ≤ K σ) :
    restrictedSpinLog S H ≤ restrictedSpinLog T K := by
  apply sub_le_sub_right
  apply Real.log_le_log (Finset.sum_pos (fun σ _ => Real.exp_pos (H σ)) hS)
  exact (Finset.sum_le_sum (fun σ hσ => Real.exp_le_exp.mpr (hHK σ hσ))).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hST (fun σ _ _ => (Real.exp_pos (K σ)).le))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldScalarSecondDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded second derivatives through the actual finite scalar recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldScalarSecondCap (L : List (ℝ × ℝ≥0)) (K C : ℝ) : ℝ :=
  L.foldr (fun av c => c + 2 * |av.1| * K ^ 2) C

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldScalarLogCoshSecond
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded first and second spatial derivatives for the scalar Ising
backward recursion, including degenerate covariance increments. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma field_tanh_second_bound (z : ℝ) : |1 / (Real.cosh z) ^ 2| ≤ 1 := by
  rw [abs_of_nonneg (by positivity : 0 ≤ 1 / (Real.cosh z) ^ 2)]
  apply (div_le_one (sq_pos_of_pos (Real.cosh_pos z))).mpr
  nlinarith [Real.one_le_cosh z]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldParameterGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local uniform growth follows from the actual bounded spatial
derivative and continuity of the parameter at spatial coordinate zero. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

lemma field_parameter_growth_eventually {U X : ℝ × ℝ → ℝ} {K t : ℝ}
    (_hK : 0 ≤ K) (hX : ∀ p, |X p| ≤ K)
    (hd : ∀ s y, HasDerivAt (fun z => U (s, z)) (X (s, y)) y)
    (hc : ContinuousAt (fun s => U (s, 0)) t) :
    ∀ᶠ s in 𝓝 t, ∀ y,
      |U (s, y)| ≤ |U (t, 0)| + 1 + K * |y| := by
  have he : ∀ᶠ s in 𝓝 t, |U (s, 0)| < |U (t, 0)| + 1 :=
    (tendsto_order.1 hc.abs).2 _ (lt_add_one _)
  filter_upwards [he] with s hs y
  have hdiff : |U (s, y) - U (s, 0)| ≤ K * |y| := by
    simpa only [Real.norm_eq_abs, sub_zero] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun z (_ : z ∈ (univ : Set ℝ)) => (hd s z).hasDerivWithinAt)
        (fun z _ => by simpa only [Real.norm_eq_abs] using hX (s, z))
        convex_univ (mem_univ 0) (mem_univ y)
  calc
    |U (s, y)| = |U (s, y) - U (s, 0) + U (s, 0)| := by congr 1; ring
    _ ≤ |U (s, y) - U (s, 0)| + |U (s, 0)| := abs_add_le _ _
    _ ≤ K * |y| + (|U (t, 0)| + 1) := add_le_add hdiff hs.le
    _ = _ := by ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticSpatialThird
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Third spatial differentiation of one actual Gaussian backward step.
The formula is kept as tilted averages, so it also applies to zero variance. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldThirdTransformCap (ζ K C D : ℝ) : ℝ :=
  (D + 2 * |ζ| * C * K) + |ζ| *
    ((2 * K * C + 2 * |ζ| * K ^ 2 * K) + 2 * K * (C + 2 * |ζ| * K ^ 2))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticScalarThird
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The third spatial derivative propagated through the finite scalar
recursion, with an explicit finite bound at every level. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldScalarThirdCap : List (ℝ × ℝ≥0) → ℝ → ℝ → ℝ → ℝ
  | [], _, _, D => D
  | av :: L, K, C, D => fieldThirdTransformCap av.1 K
      (fieldScalarSecondCap L K C) (fieldScalarThirdCap L K C D)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticSpatialFourth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourth spatial differentiation of the actual Gaussian field step.
The derivative is expressed in bounded tilted averages; no positive-variance
assumption is needed. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def MagneticUniformBound (f : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |f x| ≤ C

lemma magnetic_uniform_const (c : ℝ) : MagneticUniformBound (fun _ => c) :=
  ⟨|c|, abs_nonneg _, fun _ => le_rfl⟩

lemma magnetic_uniform_add {f g : ℝ → ℝ}
    (hf : MagneticUniformBound f) (hg : MagneticUniformBound g) :
    MagneticUniformBound (fun x => f x + g x) := by
  obtain ⟨C, hC, hf⟩ := hf
  obtain ⟨D, hD, hg⟩ := hg
  exact ⟨C + D, add_nonneg hC hD,
    fun x => (abs_add_le _ _).trans (add_le_add (hf x) (hg x))⟩

lemma magnetic_uniform_sub {f g : ℝ → ℝ}
    (hf : MagneticUniformBound f) (hg : MagneticUniformBound g) :
    MagneticUniformBound (fun x => f x - g x) := by
  obtain ⟨C, hC, hf⟩ := hf
  obtain ⟨D, hD, hg⟩ := hg
  exact ⟨C + D, add_nonneg hC hD,
    fun x => (abs_sub _ _).trans (add_le_add (hf x) (hg x))⟩

lemma magnetic_uniform_mul {f g : ℝ → ℝ}
    (hf : MagneticUniformBound f) (hg : MagneticUniformBound g) :
    MagneticUniformBound (fun x => f x * g x) := by
  obtain ⟨C, hC, hf⟩ := hf
  obtain ⟨D, hD, hg⟩ := hg
  refine ⟨C * D, mul_nonneg hC hD, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hf x) (hg x) (abs_nonneg _) hC

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticScalarFourth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual fourth spatial derivative through every finite backward
level. Its global bound is finite for each fixed finite field. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldLogCoshFourth (z : ℝ) : ℝ :=
  -2 * (1 / (Real.cosh z) ^ 2) ^ 2 +
    4 * (Real.tanh z) ^ 2 * (1 / (Real.cosh z) ^ 2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticContinuationRegular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability and finite spatial derivative bounds for the actual
Gaussian continuation formulas through order three. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def MagneticContinuationBound (f : ℝ → ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ x, |f x| ≤ K

namespace MagneticContinuationBound

lemma const (c : ℝ) : MagneticContinuationBound (fun _ => c) :=
  ⟨|c|, abs_nonneg _, fun _ => le_rfl⟩

lemma add {f g : ℝ → ℝ} (hf : MagneticContinuationBound f)
    (hg : MagneticContinuationBound g) : MagneticContinuationBound (fun x => f x + g x) := by
  obtain ⟨K, hK, bK⟩ := hf
  obtain ⟨L, hL, bL⟩ := hg
  exact ⟨K + L, add_nonneg hK hL, fun x =>
    (abs_add_le _ _).trans (add_le_add (bK x) (bL x))⟩

lemma sub {f g : ℝ → ℝ} (hf : MagneticContinuationBound f)
    (hg : MagneticContinuationBound g) : MagneticContinuationBound (fun x => f x - g x) := by
  obtain ⟨K, hK, bK⟩ := hf
  obtain ⟨L, hL, bL⟩ := hg
  exact ⟨K + L, add_nonneg hK hL, fun x =>
    (abs_sub _ _).trans (add_le_add (bK x) (bL x))⟩

lemma mul {f g : ℝ → ℝ} (hf : MagneticContinuationBound f)
    (hg : MagneticContinuationBound g) : MagneticContinuationBound (fun x => f x * g x) := by
  obtain ⟨K, hK, bK⟩ := hf
  obtain ⟨L, hL, bL⟩ := hg
  refine ⟨K * L, mul_nonneg hK hL, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (bK x) (bL x) (abs_nonneg _) hK

end MagneticContinuationBound

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticContinuationJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded third-order spatial jet for the finite Ising continuation.
Only the square and actual Gaussian transition operations are required. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

structure MagneticContinuationJet where
  value : ℝ → ℝ
  first : ℝ → ℝ
  second : ℝ → ℝ
  third : ℝ → ℝ
  mValue : Measurable value
  mFirst : Measurable first
  mSecond : Measurable second
  mThird : Measurable third
  bValue : MagneticContinuationBound value
  bFirst : MagneticContinuationBound first
  bSecond : MagneticContinuationBound second
  bThird : MagneticContinuationBound third
  dValue : ∀ z, HasDerivAt value (first z) z
  dFirst : ∀ z, HasDerivAt first (second z) z
  dSecond : ∀ z, HasDerivAt second (third z) z

namespace MagneticContinuationJet

def square (A : MagneticContinuationJet) : MagneticContinuationJet where
  value := fun z => (A.value z) ^ 2
  first := fun z => 2 * A.value z * A.first z
  second := fun z => 2 * (A.first z) ^ 2 + 2 * A.value z * A.second z
  third := fun z => 6 * A.first z * A.second z + 2 * A.value z * A.third z
  mValue := A.mValue.pow_const 2
  mFirst := (measurable_const.mul A.mValue).mul A.mFirst
  mSecond := (measurable_const.mul (A.mFirst.pow_const 2)).add
    ((measurable_const.mul A.mValue).mul A.mSecond)
  mThird := ((measurable_const.mul A.mFirst).mul A.mSecond).add
    ((measurable_const.mul A.mValue).mul A.mThird)
  bValue := by simpa only [pow_two] using A.bValue.mul A.bValue
  bFirst := ((MagneticContinuationBound.const 2).mul A.bValue).mul A.bFirst
  bSecond := by
    have hs : MagneticContinuationBound (fun z => (A.first z) ^ 2) := by
      simpa only [pow_two] using A.bFirst.mul A.bFirst
    exact ((MagneticContinuationBound.const 2).mul hs).add
      (((MagneticContinuationBound.const 2).mul A.bValue).mul A.bSecond)
  bThird := (((MagneticContinuationBound.const 6).mul A.bFirst).mul A.bSecond).add
    (((MagneticContinuationBound.const 2).mul A.bValue).mul A.bThird)
  dValue := fun z => by
    convert (A.dValue z).pow 2 using 1
    all_goals try with_reducible_and_instances rfl
    ring
  dFirst := fun z => by
    convert ((A.dValue z).const_mul 2).mul (A.dFirst z) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  dSecond := fun z => by
    convert (((A.dFirst z).pow 2).const_mul 2).add
      (((A.dValue z).const_mul 2).mul (A.dSecond z)) using 1
    all_goals try with_reducible_and_instances rfl
    ring

end MagneticContinuationJet
end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticJetProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite third-order product needed for the fourth derivative of the
actual scalar Gaussian transition. -/

noncomputable section
open MeasureTheory

namespace InvariantIsing
lemma MagneticContinuationJet.eq_of_value_eq (A B : MagneticContinuationJet)
    (h : A.value = B.value) : A = B := by
  have h1 : A.first = B.first := by
    funext z
    exact (A.dValue z).unique (h ▸ B.dValue z)
  have h2 : A.second = B.second := by
    funext z
    exact (A.dFirst z).unique (h1 ▸ B.dFirst z)
  have h3 : A.third = B.third := by
    funext z
    exact (A.dSecond z).unique (h2 ▸ B.dSecond z)
  cases A
  cases B
  cases h
  cases h1
  cases h2
  cases h3
  rfl

namespace MagneticContinuationJet

def mul (A B : MagneticContinuationJet) : MagneticContinuationJet where
  value := fun z => A.value z * B.value z
  first := fun z => A.first z * B.value z + A.value z * B.first z
  second := fun z => A.second z * B.value z + 2 * A.first z * B.first z + A.value z * B.second z
  third := fun z => A.third z * B.value z + 3 * A.second z * B.first z +
    3 * A.first z * B.second z + A.value z * B.third z
  mValue := A.mValue.mul B.mValue
  mFirst := (A.mFirst.mul B.mValue).add (A.mValue.mul B.mFirst)
  mSecond := ((A.mSecond.mul B.mValue).add ((measurable_const.mul A.mFirst).mul B.mFirst)).add
    (A.mValue.mul B.mSecond)
  mThird := (((A.mThird.mul B.mValue).add ((measurable_const.mul A.mSecond).mul B.mFirst)).add
    ((measurable_const.mul A.mFirst).mul B.mSecond)).add (A.mValue.mul B.mThird)
  bValue := A.bValue.mul B.bValue
  bFirst := (A.bFirst.mul B.bValue).add (A.bValue.mul B.bFirst)
  bSecond := ((A.bSecond.mul B.bValue).add
    (((MagneticContinuationBound.const 2).mul A.bFirst).mul B.bFirst)).add (A.bValue.mul B.bSecond)
  bThird := (((A.bThird.mul B.bValue).add
    (((MagneticContinuationBound.const 3).mul A.bSecond).mul B.bFirst)).add
    (((MagneticContinuationBound.const 3).mul A.bFirst).mul B.bSecond)).add (A.bValue.mul B.bThird)
  dValue := fun z => (A.dValue z).mul (B.dValue z)
  dFirst := fun z => by
    convert ((A.dFirst z).mul (B.dValue z)).add ((A.dValue z).mul (B.dFirst z)) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  dSecond := fun z => by
    convert (((A.dSecond z).mul (B.dValue z)).add
      (((A.dFirst z).const_mul 2).mul (B.dFirst z))).add
        ((A.dValue z).mul (B.dSecond z)) using 1
    all_goals try with_reducible_and_instances rfl
    ring

end MagneticContinuationJet
end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFourJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One additional bounded spatial derivative, exactly as needed to
differentiate the inverse-coordinate curvature equation. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

structure MagneticContinuationFourJet extends MagneticContinuationJet where
  fourth : ℝ → ℝ
  mFourth : Measurable fourth
  bFourth : MagneticContinuationBound fourth
  dThird : ∀ z, HasDerivAt third (fourth z) z

namespace MagneticContinuationFourJet

def slope (A : MagneticContinuationFourJet) : MagneticContinuationJet where
  value := A.first
  first := A.second
  second := A.third
  third := A.fourth
  mValue := A.mFirst
  mFirst := A.mSecond
  mSecond := A.mThird
  mThird := A.mFourth
  bValue := A.bFirst
  bFirst := A.bSecond
  bSecond := A.bThird
  bThird := A.bFourth
  dValue := A.dFirst
  dFirst := A.dSecond
  dSecond := A.dThird

def square (A : MagneticContinuationFourJet) : MagneticContinuationFourJet where
  toMagneticContinuationJet := A.toMagneticContinuationJet.square
  fourth := fun z => 6 * (A.second z) ^ 2 + 8 * A.first z * A.third z + 2 * A.value z * A.fourth z
  mFourth := ((measurable_const.mul (A.mSecond.pow_const 2)).add
    ((measurable_const.mul A.mFirst).mul A.mThird)).add
      ((measurable_const.mul A.mValue).mul A.mFourth)
  bFourth := by
    have h2 : MagneticContinuationBound (fun z => (A.second z) ^ 2) := by
      simpa only [pow_two] using A.bSecond.mul A.bSecond
    exact (((MagneticContinuationBound.const 6).mul h2).add
      (((MagneticContinuationBound.const 8).mul A.bFirst).mul A.bThird)).add
        (((MagneticContinuationBound.const 2).mul A.bValue).mul A.bFourth)
  dThird := fun z => by
    convert (config := {transparency := .instances, preTransparency := .instances}) (((A.dFirst z).const_mul 6).mul (A.dSecond z)).add
      (((A.dValue z).const_mul 2).mul (A.dThird z)) using 1
    · funext y
      dsimp only [MagneticContinuationJet.square, Pi.add_apply, Pi.mul_apply]
    · ring

end MagneticContinuationFourJet
end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticContinuationTwoJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The variance generator requires only two derivatives of its bounded
test. In particular it applies to the ordinary curvature without
requiring a fifth derivative of the finite scalar field. -/

noncomputable section
open MeasureTheory

namespace InvariantIsing

structure MagneticContinuationTwoJet where
  value : ℝ → ℝ
  first : ℝ → ℝ
  second : ℝ → ℝ
  mValue : Measurable value
  mFirst : Measurable first
  mSecond : Measurable second
  bValue : MagneticContinuationBound value
  bFirst : MagneticContinuationBound first
  bSecond : MagneticContinuationBound second
  dValue : ∀ z, HasDerivAt value (first z) z
  dFirst : ∀ z, HasDerivAt first (second z) z

def MagneticContinuationJet.toTwoJet (P : MagneticContinuationJet) :
    MagneticContinuationTwoJet where
  value := P.value
  first := P.first
  second := P.second
  mValue := P.mValue
  mFirst := P.mFirst
  mSecond := P.mSecond
  bValue := P.bValue
  bFirst := P.bFirst
  bSecond := P.bSecond
  dValue := P.dValue
  dFirst := P.dFirst

def MagneticContinuationJet.slopeTwoJet (P : MagneticContinuationJet) :
    MagneticContinuationTwoJet where
  value := P.first
  first := P.second
  second := P.third
  mValue := P.mFirst
  mFirst := P.mSecond
  mSecond := P.mThird
  bValue := P.bFirst
  bFirst := P.bSecond
  bSecond := P.bThird
  dValue := P.dFirst
  dFirst := P.dSecond

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticUniformSlabBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial bounds for the actual Gaussian transition, uniform in its
variance. These are used to control both endpoints of inverse coordinates. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def MagneticSlabBound (f : ℝ≥0 → ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ v z, |f v z| ≤ C

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_ConsecutiveFieldPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A repeated constrained block contributes its exact deterministic
external-field term to the full pressure. -/
noncomputable section
open IsingPerceptron
open scoped BigOperators
namespace InvariantIsing

def consecutiveBlockField {n : ℕ} (K : ℕ) (b : Fin n → ℝ) : Fin (K*n) → ℝ :=
  fun i => b (finProdFinEquiv.symm i).2

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

def canonicalFieldLabel {A : Type*} [Fintype A] (a0 : A) (s : A → ℕ)
    (N : ℕ) : Fin N → A :=
  let E := Fintype.equivFin A
  fun i => E.symm (cavityResidueLabel
    (Fintype.card_pos_iff.mpr ⟨a0⟩) (fun j => s (E.symm j)) (Equiv.sum_comp E.symm s) N i)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_UnitBilinearNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Euclidean operator norm as the supremum of unit bilinear tests. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace
namespace InvariantIsing

abbrev UnitVector (E : Type*) [NormedAddCommGroup E] := {x : E // ‖x‖ = 1}

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_CascadeSeedLeaf
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weight-preserving leaf map for ancestor-dependent vector marks. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing
variable {ι : Type}

def cascadeSeedLeaf : (n : ℕ) →
    (ℕ → (ι → ℝ) → unitInterval → (ι → ℝ)) → (ι → ℝ) →
      NoiseLeaf unitInterval n → NoiseLeaf (ι → ℝ) n
  | 0, _, _, _ => PUnit.unit
  | n+1, ψ, z, v =>
    (v.1,(ψ 0 z v.2.1,
      cascadeSeedLeaf n (fun j => ψ (j+1)) (z+ψ 0 z v.2.1) v.2.2))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_CascadeSeedPath
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ancestor-state increment path generated by an independent seed forest. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing
variable {ι : Type}

def cascadeSeedPath : (n : ℕ) → (ℕ → (ι → ℝ) → unitInterval → (ι → ℝ)) →
    (ι → ℝ) → MarkForest unitInterval n → LabeledLeaf n → Fin n → (ι → ℝ)
  | 0, _, _, _, _ => Fin.elim0
  | n+1, ψ, z, g, α =>
      Fin.cons (ψ 0 z (g α.1.1 α.1.2).1)
        (cascadeSeedPath n (fun j => ψ (j+1)) (z+ψ 0 z (g α.1.1 α.1.2).1)
          (g α.1.1 α.1.2).2 α.2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_LabeledScaledAncestry
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive ancestor-dependent reweighting preserves the sampled branch labels. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal
namespace InvariantIsing
variable {A S : Type} [MeasurableSpace A]

def ScaledLabelSimple : (n : ℕ) → (ℕ → S × A → ℝ) → (ℕ → S × A → S) →
    S → LabeledTree n → MarkForest A n → Prop
  | 0, _, _, _, _, _ => True
  | n+1, c, u, s, ω, z =>
      (∀ a b : ChildLabel, a.2 < (ω.1 a.1).1 → b.2 < (ω.1 b.1).1 →
        c 0 (s,(z a.1 a.2).1) * (ω.1 a.1).2 a.2 =
          c 0 (s,(z b.1 b.2).1) * (ω.1 b.1).2 b.2 → a = b) ∧
      ∀ a : ChildLabel, ScaledLabelSimple n (fun j => c (j+1)) (fun j => u (j+1))
        (u 0 (s,(z a.1 a.2).1)) (ω.2 a.1 a.2) (z a.1 a.2).2

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

abbrev PriorFrozenData (N j : ℕ) := SpecialOrthogonal N × OtherNamespaces (j+1)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_VectorGaussianTransition
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

def vectorShiftGaussianKernel (N : ℕ) (v : ℝ≥0) : Kernel (Fin N → ℝ) (Fin N → ℝ) :=
  fieldVectorTransitionKernel N 0 v (fun _ => 0) measurable_const

def vectorGaussianTransition (N : ℕ) (a : ℝ) (v : ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) : Kernel (Fin N → ℝ) (Fin N → ℝ) := by
  have hW : Measurable (fun y : Fin N → ℝ => ENNReal.ofReal (Real.exp (a * F y))) :=
    (hF.const_mul a).exp.ennreal_ofReal
  have hm := measurable_normalizeMass.comp
    ((measurable_withDensity_fixed hW).comp (vectorShiftGaussianKernel N v).measurable)
  exact ⟨fun z => normalizeMass ((vectorShiftGaussianKernel N v z).withDensity
    (fun y => ENNReal.ofReal (Real.exp (a * F y)))), hm⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_VectorTerminalLabeled
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
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

abbrev VectorTerminalCoordinates (N n : ℕ) := LabeledTree n × (ForestVertex n → Fin N → ℝ)

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

def positiveResolventTest (t x : ℝ) : ℝ := 1/(t+max x 0)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialDerivation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial directional derivatives for left matrix multiplication. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

abbrev MatrixPolynomial (N : ℕ) := MvPolynomial (Fin N × Fin N) ℝ

/-- Differentiate a matrix polynomial along the vector field `U ↦ A U`. -/
def matrixPolynomialDerivation {N : ℕ} :
    Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] Derivation ℝ (MatrixPolynomial N) (MatrixPolynomial N) where
  toFun A := MvPolynomial.mkDerivation ℝ fun ij =>
    ∑ k, A ij.1 k • MvPolynomial.X (k,ij.2)
  map_add' A B := by
    apply MvPolynomial.derivation_ext
    intro ij
    simp [MvPolynomial.mkDerivation_X,Matrix.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' c A := by
    apply MvPolynomial.derivation_ext
    intro ij
    simp [MvPolynomial.mkDerivation_X,Matrix.smul_apply,smul_smul,Finset.smul_sum]

@[simp] lemma matrixPolynomialDerivation_X {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    matrixPolynomialDerivation A (X (i,j)) = ∑ k, A i k • X (k,j) :=
  MvPolynomial.mkDerivation_X _ _ _

@[simp] lemma matrixPolynomialDerivation_plane_X {N : ℕ} (i j k l : Fin N) :
    matrixPolynomialDerivation (planeGenerator i j) (X (k,l)) =
      (if k=i then X (j,l) else 0)-(if k=j then X (i,l) else 0) := by
  simp [matrixPolynomialDerivation_X,planeGenerator,Matrix.single_apply,ite_and,eq_comm]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evaluation of polynomial Lie derivatives on genuine matrix curves. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

def matrixPolynomialEval {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) :
    MatrixPolynomial N →ₐ[ℝ] ℝ :=
  MvPolynomial.aeval fun ij => M ij.1 ij.2

@[simp] lemma matrixPolynomialEval_X {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    matrixPolynomialEval M (X (i,j)) = M i j :=
  MvPolynomial.aeval_X _ _

@[simp] lemma matrixPolynomialEval_C {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℝ) (c : ℝ) :
    matrixPolynomialEval M (C c) = c :=
  MvPolynomial.aeval_C _ _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialLaplacian
attribute [-simp] _root_.OAI.InvariantIsing.matrixPolynomialEval_C _root_.OAI.InvariantIsing.matrixPolynomialEval_X
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

def matrixPolynomialOperator {N : ℕ} :
    Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] Module.End ℝ (MatrixPolynomial N) where
  toFun A := (matrixPolynomialDerivation A).toLinearMap
  map_add' A B := by ext p; simp
  map_smul' c A := by ext p; simp

@[simp] lemma matrixPolynomialOperator_apply {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (p : MatrixPolynomial N) :
    matrixPolynomialOperator A p = matrixPolynomialDerivation A p := rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarDifferentiableCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-coordinate differentiable curves and their polynomial oscillation bounds. -/
noncomputable section
open Matrix Set
open scoped BigOperators
namespace InvariantIsing

structure HaarDifferentiableCurve (N : ℕ) where
  value : ℝ → SpecialOrthogonal N
  velocity : ℝ → Matrix (Fin N) (Fin N) ℝ
  hasDeriv : ∀ t ∈ Icc (0:ℝ) 1, ∀ i j,
    HasDerivAt (fun s => (value s : Matrix (Fin N) (Fin N) ℝ) i j) (velocity t i j) t
  continuous_velocity : ∀ i j, ContinuousOn (fun t => velocity t i j) (Icc (0:ℝ) 1)

namespace HaarDifferentiableCurve

lemma continuous_entry {N : ℕ} (γ : HaarDifferentiableCurve N) (i j : Fin N) :
    ContinuousOn (fun t => (γ.value t : Matrix (Fin N) (Fin N) ℝ) i j) (Icc (0:ℝ) 1) :=
  fun t ht => (γ.hasDeriv t ht i j).continuousAt.continuousWithinAt

def constant {N : ℕ} (U : SpecialOrthogonal N) : HaarDifferentiableCurve N where
  value := fun _ => U
  velocity := fun _ => 0
  hasDeriv := fun t _ _ _ => hasDerivAt_const t _
  continuous_velocity := fun _ _ => continuousOn_const

def mul {N : ℕ} (γ η : HaarDifferentiableCurve N) : HaarDifferentiableCurve N where
  value := fun t => γ.value t*η.value t
  velocity := fun t => γ.velocity t*(η.value t : Matrix (Fin N) (Fin N) ℝ)+
    (γ.value t : Matrix (Fin N) (Fin N) ℝ)*η.velocity t
  hasDeriv := by
    intro t ht i j
    have hd := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
      (γ.hasDeriv t ht i k).mul (η.hasDeriv t ht k j)
    convert (config := {transparency := .instances, preTransparency := .instances}) hd using 1
    · rfl
    · simp only [Matrix.add_apply,Matrix.mul_apply,Finset.sum_add_distrib]
  continuous_velocity := by
    intro i j
    simp only [Matrix.add_apply,Matrix.mul_apply]
    exact (continuousOn_finsetSum _ fun k _ =>
      (γ.continuous_velocity i k).mul (η.continuous_entry k j)).add
        (continuousOn_finsetSum _ fun k _ =>
          (γ.continuous_entry i k).mul (η.continuous_velocity k j))

end HaarDifferentiableCurve
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

def haarPolynomialAtom {N : ℕ} : Option (Fin N × Fin N) → MatrixPolynomial N
  | none => 1
  | some ij => X ij

def haarPolynomialWord {N d : ℕ} (w : Fin d → Option (Fin N × Fin N)) : MatrixPolynomial N :=
  ∏ k, haarPolynomialAtom (w k)

def haarPolynomialSpace (N d : ℕ) : Submodule ℝ (MatrixPolynomial N) :=
  Submodule.span ℝ (Set.range (@haarPolynomialWord N d))

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

abbrev HaarPolynomialCoordinates (N d : ℕ) :=
  Fin (Module.finrank ℝ (haarPolynomialSpace N d)) → ℝ

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

def reflectionNormalSegment {N : ℕ} (v w : EuclideanSpace ℝ (Fin N)) (t : ℝ) :
    EuclideanSpace ℝ (Fin N) := (1-t) • v+t • w

end InvariantIsing

end

end OAI
end



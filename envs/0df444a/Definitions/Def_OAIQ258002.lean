-- Prove2me | Definitions.Def_OAIQ258002
-- name    : OAIQ258002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T05:10:50.97621+00:00
-- url     : https://prove2.me/theorems/54d43891-b928-4bb5-bbd7-095600cf94a0
-- title:
--   Definitions bundle OAIQ258002 of the split of OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 301 declarations of OpenAI's Lean: 196 definitions, 1 inductive type or structure, 11 instances and 93 theorems. The definitions and types are `OAI.InvariantIsing.cavityDiagonalIndex`, `OAI.InvariantIsing.compactClippedLaw`, `OAI.InvariantIsing.compactSpectralClip`, `OAI.InvariantIsing.consecutiveBlockSitePermutation`, `OAI.InvariantIsing.consecutiveSiteGroup`, `OAI.InvariantIsing.contactFieldStep`, `OAI.InvariantIsing.coordinatePairData`, `OAI.InvariantIsing.diagonalContactRate`, `OAI.InvariantIsing.diagonalMinimumCenter`, `OAI.InvariantIsing.expectedDiagonalWard`, `OAI.InvariantIsing.expectedReplicaWard`, `OAI.InvariantIsing.fieldAdjacentIncrements`, `OAI.InvariantIsing.fieldAdjacentLevel`, `OAI.InvariantIsing.fieldAppendIndex`, `OAI.InvariantIsing.fieldApproxDenominator`, `OAI.InvariantIsing.fieldApproxWeights`, `OAI.InvariantIsing.fieldAtomMass`, `OAI.InvariantIsing.fieldCascadeVariance`, `OAI.InvariantIsing.fieldCutSequence`, `OAI.InvariantIsing.fieldFoldedWeight`, `OAI.InvariantIsing.fieldHeightBox`, `OAI.InvariantIsing.fieldHeightEpsilon`, `OAI.InvariantIsing.fieldHeightIncrement`, `OAI.InvariantIsing.fieldHeightSlope`, `OAI.InvariantIsing.fieldLabelInjection`, `OAI.InvariantIsing.fieldLevelIndex`, `OAI.InvariantIsing.fieldObservableDifferential`, `OAI.InvariantIsing.fieldPartitionConstant`, `OAI.InvariantIsing.fieldPrefixIndex`, `OAI.InvariantIsing.fieldScaleCovariance`, `OAI.InvariantIsing.fieldScaleIncrements`, `OAI.InvariantIsing.fieldSplitIndex`, `OAI.InvariantIsing.fieldStrictHeightCone`, `OAI.InvariantIsing.fieldTail`, `OAI.InvariantIsing.fieldTailVariance`, `OAI.InvariantIsing.fieldTerminalIncrements`, `OAI.InvariantIsing.fieldTerminalLevel`, `OAI.InvariantIsing.fieldVaryingCap`, `OAI.InvariantIsing.fieldWeightDifferential`, `OAI.InvariantIsing.finiteGaussianLogPartition` and 157 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `InvariantIsing_Arrays_CoordinatePairData`, `InvariantIsing_Arrays_CountableWardFunctional`, `InvariantIsing_Arrays_FullPerturbationMinima`, `InvariantIsing_Arrays_MonomialEnumeration`, `InvariantIsing_Arrays_OverlapPathCompact`, `InvariantIsing_Arrays_PerturbationMinimumRates`, `InvariantIsing_Arrays_QuantileProductPath`, `InvariantIsing_Arrays_ReplicaContractions`, `InvariantIsing_Arrays_ReplicaPairLaw`, `InvariantIsing_Arrays_ReplicaProductContinuity`, `InvariantIsing_Arrays_ReplicaWardPaths`, `InvariantIsing_Arrays_TensorAmplitudeComparison`, `InvariantIsing_Arrays_TensorContactStep`, `InvariantIsing_Arrays_TensorDiagonalPrincipalObservables`, `InvariantIsing_Arrays_TensorDiagonalPrincipalWard`, `InvariantIsing_Arrays_TensorKernelDiagonalError`, `InvariantIsing_Arrays_TensorLimitingDiagonal`, `InvariantIsing_Arrays_TensorMinimumPenalty`, `InvariantIsing_Arrays_TensorPrincipalObservables`, `InvariantIsing_Arrays_TripleContractions`, `InvariantIsing_Arrays_UltrametricProduct`, `InvariantIsing_Cavity_CavityResidualReplica`, `InvariantIsing_Cavity_CavitySlowDepth`, `InvariantIsing_Cavity_ConsecutiveBlockPrior`, `InvariantIsing_Cavity_ConsecutiveGroupProfile`, `InvariantIsing_Cavity_OffsetBlockSymmetry`, `InvariantIsing_Cavity_OffsetFieldPopulation`, `InvariantIsing_Core_DenseFiniteMaximum`, `InvariantIsing_Core_DenseFiniteMinimum`, `InvariantIsing_Core_FiniteFieldAtomMass`, `InvariantIsing_Core_FiniteFieldLawCoupling`, `InvariantIsing_Core_FiniteFieldMatching`, `InvariantIsing_Core_FiniteGaussianMaximum`, `InvariantIsing_Core_FiniteGaussianVariance`, `InvariantIsing_Core_FiniteIndexCoupling`, `InvariantIsing_Core_FiniteIndexDistribution`, `InvariantIsing_Core_FiniteMinmax`, `InvariantIsing_Core_FinitePopulationCoupling`, `InvariantIsing_Core_FinitePushforwardEntropy`, `InvariantIsing_Core_FiniteSpinEntropy`, `InvariantIsing_Core_KernelRelativeEntropy`, `InvariantIsing_Core_PositiveRationalApproximation`, `InvariantIsing_Fields_CascadeTilt`, `InvariantIsing_Fields_FieldBounds`, `InvariantIsing_Fields_FieldCapEstimate`, `InvariantIsing_Fields_FieldCascade`, `InvariantIsing_Fields_FieldCoordinateDerivative`, `InvariantIsing_Fields_FieldFiniteDomain`, `InvariantIsing_Fields_FieldFoldedKernel`, `InvariantIsing_Fields_FieldHeightBox`, `InvariantIsing_Fields_FieldHeightCone`, `InvariantIsing_Fields_FieldHeightJoint`, `InvariantIsing_Fields_FieldHeightRegularization`, `InvariantIsing_Fields_FieldHeightUpdate`, `InvariantIsing_Fields_FieldLevelPath`, `InvariantIsing_Fields_FieldMagnetization`, `InvariantIsing_Fields_FieldRadialCovariance`, `InvariantIsing_Fields_FieldRefineMagnetization`, `InvariantIsing_Fields_FieldScalarComposition`, `InvariantIsing_Fields_FieldScalarLogCoshSecond`, `InvariantIsing_Fields_FieldScalarScaling`, `InvariantIsing_Fields_FieldSquarePrefix`, `InvariantIsing_Fields_FieldTail`, `InvariantIsing_Fields_FieldTailMgf`, `InvariantIsing_Fields_FieldTiltedFamilyDerivative`, `InvariantIsing_Fields_FieldVaryingRecursion`, `InvariantIsing_Fields_MarkEndpointIntegral`, `InvariantIsing_Fields_MarkEndpointKernel`, `InvariantIsing_Fields_MarkPairRecursion`, `InvariantIsing_Fields_NoiseLeafAncestry`, `InvariantIsing_Fields_NoiseReplicaPairData`, `InvariantIsing_Fields_PoissonLabeledWeights`, `InvariantIsing_Fields_PositiveFieldApproximation`, `InvariantIsing_Fields_SeedPairRecursion`, `InvariantIsing_Fields_SimpleFieldData`, `InvariantIsing_Fields_SpinCountMagnetization`, `InvariantIsing_Fields_SpinGroupCountVariance`, `InvariantIsing_Fields_SpinGroupProjection`, `InvariantIsing_Fields_SpinGroupSlice`, `InvariantIsing_Fields_VectorTerminalCascade`, `InvariantIsing_Fields_VectorTerminalNoise`, `InvariantIsing_Gaussian_GaussianColumnDeviation`, `InvariantIsing_Gaussian_GaussianColumnProductLaw`, `InvariantIsing_Gaussian_GaussianCompactVariance`, `InvariantIsing_Gaussian_GaussianConeCutoff`, `InvariantIsing_Gaussian_GaussianCoordinateNorm`, `InvariantIsing_Gaussian_GaussianDiagonalQuadratic`, `InvariantIsing_Gaussian_GaussianGramColumns`, `InvariantIsing_Gaussian_GaussianGramResolventEquation`, `InvariantIsing_Gaussian_GaussianLeaveOneColumn`, `InvariantIsing_Gaussian_GaussianPatternEuclideanNorm`, `InvariantIsing_Gaussian_GaussianPatternSingularMinimum`, `InvariantIsing_Gaussian_GaussianQuadraticPotential`, `InvariantIsing_Gaussian_GaussianSmoothing`, `InvariantIsing_Gaussian_GaussianTranspose`, `InvariantIsing_Gaussian_GordonWeights`, `InvariantIsing_Gaussian_HermitianGaussianQuadratic`, `InvariantIsing_Gaussian_IndexedGaussianMaximum`, `InvariantIsing_Gaussian_MPAngularCoordinates`, `InvariantIsing_Gaussian_MPAngularIntegrability`, `InvariantIsing_Gaussian_MPAngularMass`, `InvariantIsing_Gaussian_MPDensityIntegrability`, `InvariantIsing_Gaussian_MPDensityProbability`, `InvariantIsing_Gaussian_MPDensitySubstitution`, `InvariantIsing_Gaussian_MPEdgeArithmetic`, `InvariantIsing_Gaussian_MPTrigonometricCritical`, `InvariantIsing_Gaussian_MPTrigonometricDenominator`, `InvariantIsing_Gaussian_MPTrigonometricIntegral`, `InvariantIsing_Gaussian_MPTrigonometricPrimitive`, `InvariantIsing_Gaussian_MarchenkoPasturTransform`, `InvariantIsing_Haar_HaarCompactness`, `InvariantIsing_Haar_HaarFrobeniusBracket`, `InvariantIsing_Haar_HaarPolynomialRotation`, `InvariantIsing_Haar_PlaneRotation`, `InvariantIsing_Haar_PositiveExponentialSum`, `InvariantIsing_Haar_RotationMatrix`, `InvariantIsing_Magnetic_MagneticAdjacentCurvature`, `InvariantIsing_Magnetic_MagneticBlockError`, `InvariantIsing_Magnetic_MagneticFieldLevels`, `InvariantIsing_Magnetic_MagneticFiniteFourth`, `InvariantIsing_Magnetic_MagneticGaussianCovariance`, `InvariantIsing_Magnetic_MagneticPopulationCoupling`, `InvariantIsing_Magnetic_MagneticPrefixComparison`, `InvariantIsing_Magnetic_MagneticRelativeThird`, `InvariantIsing_Magnetic_MagneticRoundedCount`, `InvariantIsing_Magnetic_MagneticScalarThird`, `InvariantIsing_Magnetic_MagneticScaledSlab`, `InvariantIsing_Magnetic_MagneticSlabCoefficient`, `InvariantIsing_Magnetic_MagneticVariational`, `InvariantIsing_Magnetic_RestrictedKernelFactorization`, `InvariantIsing_Pressure_RandomCoefficientGG`, `InvariantIsing_Spectral_CompactSpectralClipping`, `InvariantIsing_Spectral_PositiveResolventSpectrum`, `InvariantIsing_Spectral_SpectralClipping`, `InvariantIsing_Spectral_SpectralDiagonalCenters`, `InvariantIsing_Spectral_SpectralLabelCounts`, `InvariantIsing_Spectral_SpectralPartition`, `InvariantIsing_Spectral_SpectralPartitionPaths`, `InvariantIsing_Spectral_SpectralPermutation`, `InvariantIsing_Spectral_SpectralSymbols`, `IsingPerceptron_ArrayGeometry`, `IsingPerceptron_ArraySynchronization`, `IsingPerceptron_ChildLabel`, `IsingPerceptron_ContactFaces`, `IsingPerceptron_EnergyShift`, `IsingPerceptron_EnrichedCGF`, `IsingPerceptron_FieldChain`, `IsingPerceptron_JointGGClosure`, `IsingPerceptron_MonomialGgAtMinimum`, `IsingPerceptron_NamespaceSplit`, `IsingPerceptron_NoiseGibbsRegular`, `IsingPerceptron_OrderedQuantile`, `IsingPerceptron_SamplingIndependent`, `IsingPerceptron_TiltedLabelLaw`, `IsingPerceptron_TimeIncrement`, `IsingPerceptron_VarianceDerivative`, `IsingPerceptron_VarianceOfConditionalCenterBound`, `KLS_Measures_PotentialMeasure`, `KLS_Model`, `KLS_Regularization_RegularPotential`, `KLS_Spectral_BrascampLiebMoments`, `KLS_Spectral_BrascampLiebPerturbation`, `KLS_Stein_SteinHessianDefs`.
--
--   **Imports.** It imports the published bundle `Def_InvariantIsing`; the bundle `OAIQ4Ip000` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ258003` and `OAIQ258004`; the statements `OAI.InvariantIsing.gaussianPatternSingularMax_upper_edge`, `OAI.InvariantIsing.gaussianPatternTranspose_lower_edge`, `OAI.InvariantIsing.spectral_clip_empirical_tendsto`, `OAI.InvariantIsing.spectral_clip_mean_field_pressure_close` and `OAI.InvariantIsing.spectral_clip_mean_pressure_close`; the proofs of `OAI.InvariantIsing.cavity_cascade_spin_block_tendsto`, `OAI.InvariantIsing.cavity_residual_innovation_leaf_law`, `OAI.InvariantIsing.gaussianLipschitzVariance_proved`, `OAI.InvariantIsing.gaussianNorm_lower_mean`, `OAI.InvariantIsing.gaussianPattern_spectralExcess_tendsto`, `OAI.InvariantIsing.spectral_clip_empirical_tendsto` and `OAI.IsingPerceptron.enrichedCoordinatePressure_eq_noise`.
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
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
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

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). A def, made a local instance by the port only in modules naming
`CommCStarAlgebra` or `IsMulCommutative` (`oaiport.comm_cstar_line`): as a global instance it made `whnf` time out in
FactorGeneration modules with their own `CStarAlgebra` instances on a subalgebra (oaiq-122). -/
@[reducible]
noncomputable def starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_NoiseGibbsRegular
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.markedReplicaLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Noise Gibbs Regular. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

def noiseTerminalGibbsLaw (n : ℕ) (X : ℕ → S → ℝ) (u : ℕ → S × A → S)
    (s : S) (ν : NoiseTree A n) : Measure (NoiseLeaf A n) :=
  normalizeMass ((noiseLeafKernel A n ν).withDensity
    (fun v => ENNReal.ofReal (Real.exp (noiseLeafTerminal n X u s v))))

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ChildLabel
attribute [-instance] _root_.OAI.IsingPerceptron.enrichedCoordinateLaw_probability _root_.OAI.IsingPerceptron.enrichedCylinderBaseLaw_probability _root_.OAI.IsingPerceptron.enrichedCylinderLaw_probability _root_.OAI.IsingPerceptron.labeledSpinReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Child Label. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

def labeledTreeForget : (n : ℕ) → LabeledTree n → RawTree n
  | 0, _ => PUnit.unit
  | n+1, ω => labeledMarkedMeasure (ω.1,fun m i => labeledTreeForget n (ω.2 m i))

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

lemma measurable_stoppedUpdate (n : ℕ) {u : ℕ → S × A → S}
    (hu : ∀ i, Measurable (u i)) (i : ℕ) : Measurable (stoppedUpdate n u i) := by
  unfold stoppedUpdate
  split_ifs
  · exact hu i
  · exact measurable_fst

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_VarianceOfConditionalCenterBound
attribute [-instance] _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Variance Of Conditional Center Bound. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

namespace IsingPerceptron

variable {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

omit [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma measurable_labeledEnergy (n : ℕ) (γ : LabeledLeaf n) :
    Measurable (fun p : MarkForest (I → ℝ) n × (I → ℝ) => labeledEnergy n p.1 γ p.2) := by
  induction n with
  | zero => exact measurable_snd
  | succ n ih =>
    exact (ih γ.2).comp (show Measurable (fun p : MarkForest (I → ℝ) (n+1) × (I → ℝ) =>
      ((p.1 γ.1.1 γ.1.2).2,p.2+(p.1 γ.1.1 γ.1.2).1)) from by fun_prop)

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
namespace IsingPerceptron
variable {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]


def scalarShiftLaw (μ : ProbabilityMeasure (I → ℝ)) (v : ℝ≥0) : ProbabilityMeasure (I → ℝ) :=
  ⟨((μ : Measure (I → ℝ)).prod (gaussianReal 0 v)).map
    (fun p : (I → ℝ) × ℝ => fun x => p.1 x+p.2),
    (by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

end IsingPerceptron

 

 

 

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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_NoiseLeafAncestry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Shared ancestry read from the sequence of Poisson edge weights. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

def noiseLeafCommonDepth {A B : Type} : (n : ℕ) → NoiseLeaf A n → NoiseLeaf B n → ℕ
  | 0, _, _ => 0
  | n+1, v, w => if v.1 = w.1 then 1 + noiseLeafCommonDepth n v.2.2 w.2.2 else 0

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_NoiseReplicaPairData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The joint branch-depth and two-mark-path observable on noise replicas. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

def noiseReplicaPairData {A : Type} (n : ℕ) (σ : ℕ → NoiseLeaf A n) :
    ℕ × (Fin n → A × A) :=
  (noiseLeafCommonDepth n (σ 0) (σ 1),fun i => (noiseLeafMark n (σ 0) i,noiseLeafMark n (σ 1) i))

end InvariantIsing

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
namespace IsingPerceptron

def gaussianNamespaceJoin (j : ℕ) (p : (ℕ → ℝ) × OtherNamespaces j) (i : ℕ) : ℝ :=
  if h : (Nat.unpair i).1 = j then p.1 (Nat.unpair i).2
    else p.2 ⟨(Nat.unpair i).1,h⟩ (Nat.unpair i).2

end IsingPerceptron

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_EnrichedCGF
attribute [-instance] _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enriched C G F. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron
variable {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]


def cascadeCoordinateLaw (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (I → ℝ)) :
    Measure (LabeledTree n × (ForestVertex n → I → ℝ)) :=
  (labeledCascadeLaw n b : Measure (LabeledTree n)).prod
    (Measure.infinitePi (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure (I → ℝ))))

instance cascadeCoordinateLaw_probability (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) : IsProbabilityMeasure (cascadeCoordinateLaw n b μ) := by
  unfold cascadeCoordinateLaw; infer_instance

def cascadeCoordinateEnergy (n : ℕ) (H : I → ℝ)
    (p : LabeledTree n × (ForestVertex n → I → ℝ)) (s : I × LabeledLeaf n) : ℝ :=
  H s.1+∑ i : Fin n, p.2 (edgeAt n s.2 i) s.1

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
-- module Solutions.OAIQ258_II.IsingPerceptron_VarianceDerivative
attribute [-instance] _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Variance Derivative. -/

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
variable {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]



def scalarCoordinateInsert (n : ℕ) (a : ℕ → ℝ)
    (p : (LabeledTree n × (ForestVertex n → I → ℝ)) × (ℕ → ℝ)) :
    LabeledTree n × (ForestVertex n → I → ℝ) :=
  (p.1.1,fun v x => p.1.2 v x+a (forestVertexDepth n v)*edgeGaussianCoordinates n p.2 v)

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

def cascadeCoordinateLog (n : ℕ) (ν : Measure I) (H : I → ℝ)
    (p : LabeledTree n × (ForestVertex n → I → ℝ)) : ℝ :=
  Real.log (∫ s, Real.exp (cascadeCoordinateEnergy n H p s) ∂labeledSpinReference n ν p.1)

end IsingPerceptron

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_SamplingIndependent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sampling Independent. -/

noncomputable section

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
namespace IsingPerceptron

lemma measurable_coordinateMarkPath {A : Type} [MeasurableSpace A] (n : ℕ) :
    Measurable (coordinateMarkPath (A := A) n) := by
  apply Measurable.of_eval; intro i
  apply Measurable.of_eval; intro d
  have hv : Measurable (fun p : (ForestVertex n → A) × LabeledLeaf n => p.1 (edgeAt n p.2 d)) :=
    measurable_from_prod_countable_left (fun v => measurable_pi_apply (edgeAt n v d))
  exact hv.comp (measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst))



end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma measurable_sampledMarkPath (n : ℕ) : Measurable (sampledMarkPath n) :=
  (measurable_coordinateMarkPath n).comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))


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

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_CoordinatePairData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The measurable labeled two-path observable in the original forest coordinates. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

def coordinatePairData {A : Type} (n : ℕ)
    (p : (ForestVertex n → A) × (ℕ → LabeledLeaf n)) : ℕ × (Fin n → A × A) :=
  (labeledCommonDepth n (p.2 0) (p.2 1),
    fun i => (p.1 (edgeAt n (p.2 0) i),p.1 (edgeAt n (p.2 1) i)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_CountableWardFunctional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded two- and three-replica Ward terms pass through leaf exhaustion.
A finite Ward bound is preserved in the countable-leaf limit. -/

noncomputable section

open MeasureTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

def expectedReplicaWard {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (ν : Measure X) (H : Ω × X → ℝ)
    (D₂ : Ω × (Fin 2 → X) → ℝ) (D₃ : Ω × (Fin 3 → X) → ℝ) : ℝ :=
  (∫ ω, referenceReplicaMean ν (fun x => H (ω,x)) (fun σ => D₂ (ω,σ)) ∂P) -
    2 * ∫ ω, referenceReplicaMean ν (fun x => H (ω,x)) (fun σ => D₃ (ω,σ)) ∂P

end InvariantIsing

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

def contactStep (N : ℕ) : ℝ := (N:ℝ)^(-1/4:ℝ)

end IsingPerceptron

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

def multidegreeEncode : (m : ℕ) → (Fin m → ℕ) → ℕ
  | 0, _ => 0
  | m + 1, d => Nat.pair (d 0) (multidegreeEncode m (Fin.tail d))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ArraySynchronization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Array Synchronization. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal Matrix

namespace IsingPerceptron


def negativeBlock {Ω : Type*} (B : Ω → ℕ → ℕ → ℝ) (ε : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∀ i j : Fin n, i ≠ j → B ω i j < -ε}

def permuteArray (e : Equiv.Perm ℕ) (b : RealArray) : RealArray :=
  fun i j => b (e i) (e j)

 

def WeaklyExchangeable {Ω : Type*} [MeasurableSpace Ω]
    (B : Ω → RealArray) (μ : Measure Ω) : Prop :=
  ∀ e : Equiv.Perm ℕ, {i | e i ≠ i}.Finite →
    IdentDistrib B (fun ω => permuteArray e (B ω)) μ μ



def starSet (a : ℕ) (J : Finset ℕ) (A : Set (Fin a → Fin a → ℝ))
    (T : Set (Fin a → ℝ)) (t : ℝ) (i : ℕ) : Set RealArray :=
  {b | (fun x y : Fin a => b x y) ∈ A ∧
    (fun x : Fin a => b x i) ∈ T ∧ ∀ j ∈ J, j ≠ i → b i j < t}

def duplicateSet (a : ℕ) (A : Set (Fin a → Fin a → ℝ))
    (T : Set (Fin a → ℝ)) (t : ℝ) (i j : ℕ) : Set RealArray :=
  {b | (fun x y : Fin a => b x y) ∈ A ∧
    (fun x : Fin a => b x i) ∈ T ∧
    (fun x : Fin a => b x j) ∈ T ∧ b i j < t}


def extendArrayBlock (n : ℕ) (b : Fin n → Fin n → ℝ) : RealArray :=
  fun i j => if hi : i < n then if hj : j < n then b ⟨i,hi⟩ ⟨j,hj⟩ else 0 else 0


def groupAverageMatrix {m : ℕ} (B : Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => (∑ a : Fin m, ∑ b : Fin m, B (i,a) (j,b)) / (m : ℝ)^2

def tripleLabel {n : ℕ} (i : Fin n) : Fin 3 := ⟨i.val % 3, Nat.mod_lt _ (by decide)⟩

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ArrayGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Array Geometry. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal
namespace IsingPerceptron

def overlapQuantile (μ : Measure ℝ) (u : ℝ) : ℝ :=
  sInf {x : ℝ | x ∈ Icc (0:ℝ) 1 ∧ u ≤ cdf μ x}

lemma cdf_one_of_unit_support {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hs : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) : cdf μ 1 = 1 := by
  rw [cdf_eq_real]
  have he : μ (Iic (1:ℝ)) = 1 := by
    have he' := (ae_iff_measure_eq (μ := μ) (p := fun x : ℝ => x ∈ Iic (1:ℝ)) measurableSet_Iic.nullMeasurableSet).mp
      (hs.mono (fun _ h => h.2))
    rw [measure_univ] at he'
    exact he' 
  simp [Measure.real,he]

lemma quantileSet_nonempty {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hs : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) {u : ℝ} (hu : u ≤ 1) :
    {x : ℝ | x ∈ Icc (0:ℝ) 1 ∧ u ≤ cdf μ x}.Nonempty :=
  ⟨1,⟨by norm_num,by simpa only [cdf_one_of_unit_support hs] using hu⟩⟩

lemma quantileSet_bddBelow (μ : Measure ℝ) (u : ℝ) :
    BddBelow {x : ℝ | x ∈ Icc (0:ℝ) 1 ∧ u ≤ cdf μ x} := ⟨0,fun _ h => h.1.1⟩

lemma overlapQuantile_mem {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hs : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) {u : ℝ} (hu : u ≤ 1) :
    overlapQuantile μ u ∈ Icc (0:ℝ) 1 := by
  exact ⟨le_csInf (quantileSet_nonempty hs hu) (fun _ h => h.1.1),
    (csInf_le (quantileSet_bddBelow μ u) (quantileSet_nonempty hs hu).choose_spec).trans
      (quantileSet_nonempty hs hu).choose_spec.1.2⟩


def quantileFunction (μ : Measure ℝ) (u : ℝ) : ℝ := overlapQuantile μ (min u 1)

lemma monotone_quantileFunction {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hs : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) : Monotone (quantileFunction μ) := by
  intro u v huv
  exact csInf_le_csInf (quantileSet_bddBelow μ (min u 1))
    (quantileSet_nonempty hs (min_le_right v 1))
    (fun x hx => ⟨hx.1,(min_le_min_right 1 huv).trans hx.2⟩)

lemma quantileFunction_mem {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hs : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) (u : ℝ) : quantileFunction μ u ∈ Icc (0:ℝ) 1 :=
  overlapQuantile_mem hs (min_le_right u 1)

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_OrderedQuantile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordered Quantile. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

 
def treeTail (n d : ℕ) (t : ℝ) : ℝ := max 0 (min 1 (((n+1:ℕ):ℝ)*t-d))

def treeLevels (n : ℕ) : Set ℝ := range (fun j : Fin (n+1) => (j:ℝ)/(n+1:ℕ))

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron



def finiteFieldPath {n : ℕ} (a : Fin (n+1) → ℝ) (i : ℕ) : ℝ :=
  ∑ j, if j.val ≤ i then a j else 0

lemma finiteFieldPath_nonneg {n : ℕ} {a : Fin (n+1) → ℝ} (ha : ∀ j, 0 ≤ a j) (i : ℕ) :
    0 ≤ finiteFieldPath a i := Finset.sum_nonneg (fun j _ => by split_ifs; exact ha j; exact le_refl 0)

lemma monotone_finiteFieldPath {n : ℕ} {a : Fin (n+1) → ℝ} (ha : ∀ j, 0 ≤ a j) :
    Monotone (finiteFieldPath a) := by
  intro i k hik
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j.val ≤ i
  · simp [hj,hj.trans hik]
  · simp only [hj,ite_false, if_false]
    split_ifs; exact ha j; exact le_refl 0

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_TimeIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Time Increment. -/

noncomputable section

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







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def depthTail (n j : ℕ) (t : ℝ) : ℝ := if j=0 then 1 else treeTail n (j-1) t

end IsingPerceptron

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





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def finiteStepFunction {k : ℕ} (ζ : Fin (k+1) → ℝ) (v : Fin k → ℝ) (u : ℝ) : ℝ :=
  ∑ i, if ζ i.castSucc < u ∧ u < ζ i.succ then v i else 0

end IsingPerceptron

 

 

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
-- module Solutions.OAIQ258_II.IsingPerceptron_ContactFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contact Faces. -/

noncomputable section

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





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def lowerGrid (p : ℝ → ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  (1-1/(n+1:ℕ))*p ((⌊(n+1:ℕ)*u⌋₊:ℝ)/(n+1:ℕ))

lemma lowerGrid_factor_nonneg (n : ℕ) : 0≤(1-1/(n+1:ℕ):ℝ) := by
  have h : (1:ℝ)≤(n+1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have := (div_le_one (by positivity : (0:ℝ)<(n+1:ℕ))).mpr h
  linarith

lemma lowerGrid_monotone {p : ℝ → ℝ} (hp : Monotone p) (n : ℕ) : Monotone (lowerGrid p n) := by
  intro u v huv
  apply mul_le_mul_of_nonneg_left _ (lowerGrid_factor_nonneg n)
  apply hp
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.floor_mono (mul_le_mul_of_nonneg_left huv (by positivity : (0:ℝ)≤(n+1:ℕ)))

lemma lowerGrid_mem {p : ℝ → ℝ} (hb : ∀ u, p u∈Icc (0:ℝ) 1) (n : ℕ) (u : ℝ) :
    lowerGrid p n u∈Icc (0:ℝ) 1 := by
  rcases hb ((⌊(n+1:ℕ)*u⌋₊:ℝ)/(n+1:ℕ)) with ⟨h0,h1⟩
  have hf := lowerGrid_factor_nonneg n
  dsimp only [lowerGrid]
  constructor
  · positivity
  · nlinarith [show (0:ℝ)≤1/(n+1:ℕ) by positivity]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalization of the one-site entropy

The finite Gaussian recursion agrees with the Ising recursion.
In particular the zero overlap path has entropy zero. This supplies the exact
variational normalization for a point-mass spectral law.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace InvariantIsing

/-- Extend the last covariance height constantly. -/
def heightSequence (h : FieldStep) (i : ℕ) : ℝ :=
  h.height ⟨min i h.depth, Nat.lt_succ_of_le (min_le_right _ _)⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_FiniteGaussianVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Gaussian cutoff partition functions in the Euclidean norm. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal InnerProductSpace

namespace InvariantIsing

/-- The finite-cutoff Gaussian log partition, with arbitrary probability
weights and deterministic base energy. In the application the finite state
space is a positive-mass restriction of the spin/cascade-leaf prior. -/
def finiteGaussianLogPartition {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (H : X → ℝ) {d : ℕ}
    (A : X → EuclideanSpace ℝ (Fin d)) (g : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.log (∫ x, Real.exp (H x + ⟪A x, g⟫_ℝ) ∂ν)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_RandomCoefficientGG
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! GG estimates for Haar-dependent Gaussian perturbation tensors. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

/-- Expectation over external disorder and independent Gaussian coordinates. -/
def randomCoefficientAverage (P : Measure Ω) (ν : Ω → Measure X)
    (A : Ω → X → ℕ →₀ ℝ) (t : ℝ) {r : ℕ} (D : Ω → (Fin r → X) → ℝ) : ℝ :=
  ∫ z : Ω × (ℕ → ℝ), referenceReplicaMean (ν z.1)
    (fun x => t * cylinderField (A z.1 x) z.2) (D z.1) ∂P.prod gaussianCoordinates

def randomCoefficientEnergy (P : Measure Ω) (ν : Ω → Measure X)
    (A : Ω → X → ℕ →₀ ℝ) (t : ℝ) {r : ℕ} (D : Ω → (Fin (r + 1) → X) → ℝ) : ℝ :=
  ∫ z : Ω × (ℕ → ℝ), referenceReplicaMean (ν z.1)
    (fun x => t * cylinderField (A z.1 x) z.2)
    (fun σ => cylinderField (A z.1 (σ 0)) z.2 * D z.1 σ) ∂P.prod gaussianCoordinates

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralDiagonalCenters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact deterministic centers without assuming constant finite self-overlap. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def spectralDiagonalCenter (b : ℝ) : ℝ := max 0 (min 1 b)

lemma spectralDiagonalCenter_mem (b : ℝ) : spectralDiagonalCenter b ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorKernelDiagonalError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite cascade top level is retained in each tensor diagonal center. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma finiteTreeDiagonal_mem (n : ℕ) : (n : ℝ) / (n + 1 : ℕ) ∈ Set.Icc (0 : ℝ) 1 := by
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.zero_lt_succ n
  refine ⟨div_nonneg (Nat.cast_nonneg _) hn.le, (div_le_one hn).mpr ?_⟩
  exact_mod_cast Nat.le_succ n

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_PerturbationMinimumRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vanishing rates for diagonal perturbation energies at parameter minima. -/

noncomputable section

open IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

def diagonalContactRate (N : ℕ) (L : ℝ) : ℝ :=
  let a := N * perturbationScale N
  let c := N / a ^ 2
  let θ := 1 / (Real.sqrt N * perturbationScale N)
  let δ := 2 * N * Real.sqrt (L / N)
  (2 * c + θ ^ 2) / (2 * θ) + c * (a * contactStep N) + 4 * δ / (a * contactStep N)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_FullPerturbationMinima
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! For the complete perturbation, both coordinate minima force the
Ghirlanda–Guerra errors to vanish. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def diagonalMinimumCenter (N : ℕ) (w : ℝ) : ℝ :=
  let a := N * perturbationScale N
  2 * (N / a ^ 2) * (a * w - a * (3 / 2))

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

def rationalLowerValues (f : ℚ → Icc (0 : ℝ) 1) (x : ℝ) : Set ℝ :=
  (fun q : ℚ => (f q : ℝ)) '' {q : ℚ | (q : ℝ) < x}

lemma rationalLowerValues_nonempty (f : ℚ → Icc (0 : ℝ) 1) (x : ℝ) :
    (rationalLowerValues f x).Nonempty := by
  obtain ⟨q, hq⟩ := exists_rat_lt x
  exact ⟨f q, q, hq, rfl⟩

lemma rationalLowerValues_bdd (f : ℚ → Icc (0 : ℝ) 1) (x : ℝ) :
    BddAbove (rationalLowerValues f x) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨q, _, rfl⟩
  exact (f q).property.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_ReplicaPairLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact two-link marginal of a scalar GG array. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators ENNReal

namespace InvariantIsing

def scalarOverlapLaw {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (B : Ω → RealArray) : Measure ℝ := μ.map (fun x => B x 0 1)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_UltrametricProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An atom-preserving decomposition for synchronized replica products. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators ENNReal

namespace InvariantIsing

def replicaProductFirst (a b : ℝ → ℝ) (x y : ℝ) : ℝ :=
  if y < x then a y * b y else a y * b x

def replicaProductSecond (a b : ℝ → ℝ) (x z : ℝ) : ℝ :=
  if x < z then a x * (b z - b x) else 0

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralSymbols
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Symbols of reconstructed finite spectral-group overlap paths. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

def pathSymbol (d : ℝ) (l : ℝ → ℝ) (s : ℝ) : ℝ :=
  d - s * l s - ∫ u in s..1, l u

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

def replicaProductPath (da : ℝ) (a : ℝ → ℝ) (db : ℝ) (b : ℝ → ℝ) (s : ℝ) : ℝ :=
  pathSymbol da a s * b s + a s * pathSymbol db b s + s * (a s * b s) -
    ∫ u in 0..s, a u * b u

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

/-- Coordinate evaluation of matrix-vector multiplication as a continuous
linear functional, with the Frobenius norm used only for the exponential. -/
def matrixVectorCoordinate {N : ℕ} (k : Fin N) (v : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℝ →L[ℝ] ℝ :=
  (show Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] ℝ from
    { toFun := fun M => (M *ᵥ v) k
      map_add' := by intros; simp [Matrix.add_mulVec]
      map_smul' := by intros; simp [Matrix.smul_mulVec] }).toContinuousLinearMap

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_ReplicaContractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite replica contractions in the spectral Ward calculation

The sums over two spectral coordinate groups contract into products of
projected overlaps. These are exact finite identities, with no symmetry or
full-support requirement on the deterministic spin prior.
-/

noncomputable section

open IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {S ι : Type*} [Fintype S]

/-- Independent replicas sampled from the same finite Gibbs law. -/
def gibbsPairAverage (w H : S → ℝ) (A : S → S → ℝ) : ℝ :=
  ∑ σ, ∑ τ, finiteGibbs w H σ * finiteGibbs w H τ * A σ τ

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_ReplicaProductContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The replica product is a bounded continuous function of the total
overlap when the synchronized group factors are bounded and continuous. -/

noncomputable section

open MeasureTheory IsingPerceptron Set

namespace InvariantIsing

def replicaProductKernel (ζ : Measure ℝ) (a b : ℝ → ℝ) (r : ℝ) : ℝ :=
  (∫ y, replicaProductFirst a b r y + replicaProductSecond a b r y ∂ζ) + a r * b r

def replicaProductValue (ζ : Measure ℝ) (da db : ℝ) (a b : ℝ → ℝ) (r : ℝ) : ℝ :=
  da * b r + a r * db - replicaProductKernel ζ a b r

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

def offWardPath (ρa ρb δ da db : ℝ) (a b : ℝ → ℝ) (s : ℝ) : ℝ :=
  ρa * b s - ρb * a s + δ * replicaProductPath da a db b s

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorAmplitudeComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous covariance modulus in the actual Gaussian perturbation amplitudes. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

def tensorAmplitudeModulus {k : ℕ} (a b : Fin k → ℝ) : ℝ :=
  ∑ j, |a j - b j| * (|a j| + |b j|)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldFiniteDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-step entropy is finite for trial paths bounded strictly below one. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace InvariantIsing

/-- A clamped extension used only to express finite summation by parts. -/
def fieldCutSequence (h : FieldStep) (i : ℕ) : ℝ :=
  h.cut ⟨min i (h.depth + 1), Nat.lt_succ_of_le (min_le_right _ _)⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldCapEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The rough field cap estimate used in the finite-dimensional upper comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace InvariantIsing

/-- The finite constant coming from the positive exponents of a fixed trial partition. -/
def fieldPartitionConstant (h : FieldStep) : ℝ :=
  ∑ i : Fin h.depth, Real.log 2 / (fieldIncrement h i.succ).1

def gaussianAbsoluteMean : ℝ := ∫ z : ℝ, |z| ∂gaussianReal 0 1

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorContactStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The contact increment coordinates represent the same fixed-partition
fields and pairings as the one-site variational functional. -/

noncomputable section
open MeasureTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

def contactFieldStep {n : ℕ} (cut : Fin (n + 2) → ℝ) (hc : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (a : Fin (n + 1) → ℝ) (ha : ∀ i, 0 ≤ a i) : FieldStep where
  depth := n
  cut := cut
  ordered_cut := hc
  first := hfirst
  last := hlast
  height i := finiteFieldPath a i
  nonneg i := finiteFieldPath_nonneg ha i
  ordered_height _i _j hij := monotone_finiteFieldPath ha hij

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TripleContractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replica contractions for the off-diagonal spectral Ward equation. -/

noncomputable section

open IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {S ι : Type*} [Fintype S]

def gibbsTripleAverage (w H : S → ℝ) (A : S → S → S → ℝ) : ℝ :=
  ∑ σ, ∑ τ, ∑ η, finiteGibbs w H σ * finiteGibbs w H τ * finiteGibbs w H η * A σ τ η

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

def tensorOffDirectCap {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N)) (B : ℝ) : ℝ :=
  (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K,
    (2 * N * B + (N * B) * (|eig i - eig j| * (2 * N)))

def tensorOffFreshCap {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N)) (B : ℝ) : ℝ :=
  (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K, (N * B) * (|eig i - eig j| * N)

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

def tensorDiagonalDirectCap {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N)) : ℝ :=
  (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K, ((N : ℝ) + N * (|eig i - eig j| * N))

def tensorDiagonalFreshCap {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N)) : ℝ :=
  (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K, (N : ℝ) * (|eig i - eig j| * N)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorDiagonalPrincipalWard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite diagonal principal Ward bound in original-state
one- and two-replica form, uniform in the leaf restriction. -/

noncomputable section

open MeasureTheory IsingPerceptron Filter
open scoped BigOperators Topology NNReal

namespace InvariantIsing

def expectedDiagonalWard {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (ν : Measure X) (H : Ω × X → ℝ)
    (D₁ : Ω × (Fin 1 → X) → ℝ) (D₂ : Ω × (Fin 2 → X) → ℝ) : ℝ :=
  (∫ ω, referenceReplicaMean ν (fun x => H (ω,x)) (fun σ => D₁ (ω,σ)) ∂P) -
    ∫ ω, referenceReplicaMean ν (fun x => H (ω,x)) (fun σ => D₂ (ω,σ)) ∂P

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorLimitingDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual diagonal-minimum fluctuations give constant limiting diagonals. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology

namespace InvariantIsing

def tensorMinimumArrayDiagonal {m : ℕ} (N n : ℕ) (v : Fin m → ℝ) :
    Fin (m + 1) → Set.Icc (0 : ℝ) 1 :=
  Fin.lastCases ⟨(n : ℝ) / (n + 1 : ℕ), finiteTreeDiagonal_mem n⟩
    (fun a => ⟨spectralDiagonalCenter (diagonalMinimumCenter N (v a)), spectralDiagonalCenter_mem _⟩)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorMinimumPenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual minimizing objective has a vanishing penalty whenever its
pressure has a uniform vanishing perturbation cost. Its negative minimum
is the scalar pressure envelope used in the cavity telescoping argument. -/

noncomputable section
open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def tensorMinimumPenalty {N m : ℕ} (u : Fin N → ℝ) (v : Fin m → ℝ) : ℝ :=
  (∑ j : Fin N, perturbationWeight j * (u j - 3 / 2) ^ 2) + ∑ a, (v a - 3 / 2) ^ 2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityResidualReplica
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countably many cavity replicas with one independent terminal Gaussian
residual per replica. The residual family is independent of the whole
innovation cascade, including coincidences of sampled leaves. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_measurable_prod_const {Ω X Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (κ : Measure Y) [IsProbabilityMeasure κ] :
    Measurable (fun ω => (ν ω).prod κ) := by
  let K : Kernel Ω X := ⟨ν, hν⟩
  have : IsMarkovKernel K := ⟨fun ω => by change IsProbabilityMeasure (ν ω); infer_instance⟩
  have he : (fun ω => (ν ω).prod κ) = K ×ₖ Kernel.const Ω κ := by
    funext ω
    exact (Kernel.prod_apply K (Kernel.const Ω κ) ω).symm
  rw [he]
  exact (K ×ₖ Kernel.const Ω κ).measurable

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySlowDepth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choosing system sizes fast enough for a prescribed sequence of finite
cascade depths. Each row requires only finitely many error estimates. -/

noncomputable section
open Filter IsingPerceptron
open scoped Topology

namespace InvariantIsing

def cavityDiagonalIndex (M : ℕ → ℕ) : ℕ → ℕ
  | 0 => M 0
  | r+1 => max (cavityDiagonalIndex M r+1) (M (r+1))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralPermutation
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

lemma permutationMatrix_orthogonal {N : ℕ} (p : Equiv.Perm (Fin N)) :
    p.permMatrix ℝ ∈ Matrix.orthogonalGroup (Fin N) ℝ := by
  apply (Matrix.mem_orthogonalGroup_iff (Fin N) ℝ).mpr
  rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul]
  simp

def permutationSignDiagonal {N : ℕ} (hN : 0 < N) (p : Equiv.Perm (Fin N)) :
    Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal fun i => if i = (⟨0, hN⟩ : Fin N) then (p.permMatrix ℝ).det else 1

lemma permutationSignDiagonal_det {N : ℕ} (hN : 0 < N) (p : Equiv.Perm (Fin N)) :
    (permutationSignDiagonal hN p).det = (p.permMatrix ℝ).det := by
  simp [permutationSignDiagonal, Matrix.det_diagonal]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_CascadeTilt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian `log cosh` marking preserves the unmarked cascade law. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InvariantIsing

def gaussianCascadeMarks (v : ℕ → ℝ≥0) (i : ℕ) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 (v i), (by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldFoldedKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordered folded Gaussian densities. These are the one-step comparisons
used in both the mixed and radial Ising-field derivatives. -/

noncomputable section
open MeasureTheory Set

namespace InvariantIsing

def fieldFoldedWeight (v ζ : ℝ) (F : ℝ → ℝ) (z u : ℝ) : ℝ :=
  Real.exp (-u ^ 2 / (2 * v)) * Real.cosh ((z / v) * u) * Real.exp (ζ * F u)

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

def finiteShannonEntropy {X : Type*} [Fintype X] (p : X → ℝ) : ℝ :=
  -∑ x, p x * Real.log (p x)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinGroupSlice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite magnetization slices for an arbitrary grouping of the sites.
Constant group fields factor exactly, with the original cube mass. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def spinGroupSize {N : ℕ} {A : Type*} [DecidableEq A]
    (group : Fin N → A) (a : A) : ℕ :=
  (Finset.univ.filter fun i => group i = a).card

def spinGroupCount {N : ℕ} {A : Type*} [DecidableEq A]
    (group : Fin N → A) (σ : Spin N) (a : A) : ℕ :=
  (Finset.univ.filter fun i => group i = a ∧ σ i = true).card

def spinGroupSlice {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (k : A → ℕ) : Finset (Spin N) :=
  Finset.univ.filter fun σ => ∀ a, spinGroupCount group σ a = k a

lemma spinGroupSlice_nonempty {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (k : A → ℕ) (hk : ∀ a, k a ≤ spinGroupSize group a) :
    (spinGroupSlice group k).Nonempty := by
  classical
  choose S hS hcard using fun a => Finset.exists_subset_card_eq (hk a)
  let σ : Spin N := fun i => decide (i ∈ S (group i))
  refine ⟨σ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun a => ?_⟩⟩
  have he : (Finset.univ.filter fun i => group i = a ∧ σ i = true) = S a := by
    ext i
    constructor
    · intro hi
      obtain ⟨_, hga, hpos⟩ := Finset.mem_filter.mp hi
      have hm : i ∈ S (group i) := of_decide_eq_true hpos
      simpa only [hga] using hm
    · intro hi
      have hga : group i = a := (Finset.mem_filter.mp (hS a hi)).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hga, ?_⟩
      change decide (i ∈ S (group i)) = true
      exact decide_eq_true (by simpa only [hga] using hi)
  exact (congrArg Finset.card he).trans (hcard a)

def spinGroupFieldConstant {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (k : A → ℕ) (b : A → ℝ) : ℝ :=
  ∑ a, b a * (2 * (k a : ℝ) - spinGroupSize group a)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinGroupProjection
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

lemma exists_subset_card_nearest {I : Type*} [DecidableEq I] (A S : Finset I)
    (hAS : A ⊆ S) (k : ℕ) (hk : k ≤ S.card) :
    ∃ T ⊆ S, T.card = k ∧ (A ∆ T).card = A.card - k + (k - A.card) := by
  by_cases hka : k ≤ A.card
  · obtain ⟨T, hTA, hT⟩ := Finset.exists_subset_card_eq hka
    refine ⟨T, hTA.trans hAS, hT, ?_⟩
    rw [Finset.symmDiff_def, Finset.sdiff_eq_empty_iff_subset.mpr hTA,
      Finset.union_empty, Finset.card_sdiff_of_subset hTA, hT, Nat.sub_eq_zero_of_le hka,
      Nat.add_zero]
  · have hak : A.card ≤ k := Nat.le_of_lt (Nat.lt_of_not_ge hka)
    have hrem : k - A.card ≤ (S \ A).card := by
      rw [Finset.card_sdiff_of_subset hAS]
      omega
    obtain ⟨B, hB, hBc⟩ := Finset.exists_subset_card_eq hrem
    have hd : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro i hiA hiB
      exact (Finset.mem_sdiff.mp (hB hiB)).2 hiA
    have hT : (A ∪ B).card = k := by
      rw [Finset.card_union_of_disjoint hd, hBc]
      omega
    refine ⟨A ∪ B, Finset.union_subset hAS (hB.trans Finset.sdiff_subset), hT, ?_⟩
    rw [Finset.symmDiff_def,
      Finset.sdiff_eq_empty_iff_subset.mpr Finset.subset_union_left,
      Finset.empty_union, Finset.card_sdiff_of_subset Finset.subset_union_left, hT,
      Nat.sub_eq_zero_of_le hak, Nat.zero_add]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinGroupCountVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Count fluctuations under the independent canonical site law. The
result applies to the averaged Gaussian spin kernels as soon as their
bias equations give the prescribed group means. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

namespace InvariantIsing

def spinGroupCountSummand {N : ℕ} {A : Type*} [DecidableEq A]
    (group : Fin N → A) (a : A) (i : Fin N) (b : Bool) : ℝ :=
  if group i = a ∧ b = true then 1 else 0

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

lemma field_hasDerivAt_tanh (z : ℝ) :
    HasDerivAt Real.tanh (1 / (Real.cosh z) ^ 2) z := by
  have h := (Real.hasDerivAt_sinh z).div (Real.hasDerivAt_cosh z) (Real.cosh_pos z).ne'
  have hrel := Real.cosh_sq_sub_sinh_sq z
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)).congr_deriv (Eq.symm ?_)
  · beta_reduce
    exact Real.tanh_eq_sinh_div_cosh x
  · rw [← pow_two, ← pow_two, hrel]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldScalarComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact concatenation and linear propagation identities for the finite
scalar field recursion. The exponents may include the zero root level. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

/-- Index of a level in the suffix, after an unchanged prefix. -/
def fieldAppendIndex (P S : List (ℝ × ℝ≥0)) (i : Fin (S.length + 1)) :
    Fin ((P ++ S).length + 1) :=
  ⟨P.length + i.val, by simp only [List.length_append]; omega⟩

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

/-- Actual increment list when a single nonterminal height is varied. -/
def fieldAdjacentIncrements (P S : List (ℝ × ℝ≥0)) (a b ζ η t : ℝ) :
    List (ℝ × ℝ≥0) :=
  P ++ (ζ, Real.toNNReal (a + t)) :: (η, Real.toNNReal (b - t)) :: S

def fieldAdjacentLevel (P S : List (ℝ × ℝ≥0)) (a b ζ η t : ℝ) :
    Fin ((fieldAdjacentIncrements P S a b ζ η t).length + 1) :=
  fieldAppendIndex P ((ζ, Real.toNNReal (a + t)) ::
    (η, Real.toNNReal (b - t)) :: S) 1

/-- The terminal height changes the final variance and the normalizing
subtraction by the same amount. -/
def fieldTerminalIncrements (P : List (ℝ × ℝ≥0)) (a ζ t : ℝ) :
    List (ℝ × ℝ≥0) := P ++ [(ζ, Real.toNNReal (a + t))]

def fieldTerminalLevel (P : List (ℝ × ℝ≥0)) (a ζ t : ℝ) :
    Fin ((fieldTerminalIncrements P a ζ t).length + 1) :=
  fieldAppendIndex P [(ζ, Real.toNNReal (a + t))] 1

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldLevelPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded monotone representative on the field partition. Endpoint
values are immaterial to integration; the representative is defined globally. -/

noncomputable section
open MeasureTheory Set

namespace InvariantIsing

/-- Last covariance interval whose lower endpoint has been passed. -/
def fieldLevelIndex (h : FieldStep) (s : ℝ) : Fin (h.depth + 1) :=
  Finset.univ.sup (fun i => if h.cut i.castSucc ≤ s then i else 0)

lemma fieldLevelIndex_monotone (h : FieldStep) : Monotone (fieldLevelIndex h) := by
  intro s t hst
  apply Finset.sup_le
  intro i hi
  by_cases hs : h.cut i.castSucc ≤ s
  · have ht : h.cut i.castSucc ≤ t := hs.trans hst
    have hb := Finset.le_sup (f := fun j : Fin (h.depth + 1) =>
      if h.cut j.castSucc ≤ t then j else 0) hi
    simpa only [fieldLevelIndex, hs, ht, ite_true, if_true] using hb
  · simp only [hs, ite_false, if_false]
    exact bot_le

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldMagnetization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual magnetization-overlap path for a finite scalar Ising field. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma measurable_field_tanh : Measurable Real.tanh := by
  change Measurable (fun x : ℝ => Real.tanh x)
  simp only [Real.tanh_eq]
  fun_prop

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldCascade
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite one-site functional as a Gaussian cascade expectation. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

def fieldCascadeVariance (h : FieldStep) (i : ℕ) : ℝ≥0 :=
  NNReal.mk ((IsingPerceptron.pathAmplitude (heightSequence h) (i + 1)) ^ 2)
    (sq_nonneg _)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldTailMgf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical endpoint exponential moments depend only on the sum of
increment variances. Arbitrarily small positive exponents and arbitrarily
many levels are allowed. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldTailVariance (L : List (ℝ × ℝ≥0)) : ℝ :=
  (L.map (fun av => (av.2 : ℝ))).sum

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

lemma field_logCosh_third_derivative (z : ℝ) :
    HasDerivAt (fun y : ℝ => 1 / (Real.cosh y) ^ 2)
      (-2 * Real.tanh z / (Real.cosh z) ^ 2) z := by
  have hd := (hasDerivAt_const z (1 : ℝ)).div ((Real.hasDerivAt_cosh z).pow 2)
    (pow_ne_zero 2 (Real.cosh_pos z).ne')
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Pi.pow_apply]
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual conditional squared spin means at prescribed magnetization.
The root Gaussian is averaged at the optimizing bias. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma field_measurable_tanh : Measurable Real.tanh := by
  change Measurable (fun x : ℝ => Real.tanh x)
  simp only [Real.tanh_eq]
  fun_prop

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticRelativeThird
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative third-derivative control through a physical tilted Gaussian
step. Unlike a uniform derivative bound, this remains useful at spin endpoints. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def magneticThirdRatioCap : List (ℝ × ℝ≥0) → ℝ
  | [] => 2
  | av :: L => magneticThirdRatioCap L + 8 * |av.1|

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFiniteFourth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative fourth derivatives for the actual finite Ising field recursion,
and the bounded coefficients needed for inverse-coordinate comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def magneticFourthRatioCap : List (ℝ × ℝ≥0) → ℝ
  | [] => 6
  | av :: L => magneticFourthRatioCap L + 8 * |av.1| * magneticThirdRatioCap L +
      3 * |av.1| + 37 * av.1 ^ 2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldTiltedFamilyDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiating a normalized scalar Gaussian average with a varying
observable. The local envelopes allow the affine-noise quadratic terms
needed in the second derivative of the finite Ising recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

/-- Derivative of the unnormalized Gaussian weight. -/
def fieldWeightDifferential (U : (ℝ × ℝ) → ℝ → ℝ)
    (DU : (ℝ × ℝ) → ℝ → (ℝ × ℝ) →L[ℝ] ℝ) (ζ : ℝ)
    (p : ℝ × ℝ) (u : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  Real.exp (ζ * U p u) • (ζ • DU p u)

/-- Derivative of the weighted observable. -/
def fieldObservableDifferential (U A : (ℝ × ℝ) → ℝ → ℝ)
    (DU DA : (ℝ × ℝ) → ℝ → (ℝ × ℝ) →L[ℝ] ℝ) (ζ : ℝ)
    (p : ℝ × ℝ) (u : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  Real.exp (ζ * U p u) • (DA p u + (ζ * A p u) • DU p u)

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

def magneticGaussianTime (ζ v : ℝ) (F M A B : ℝ → ℝ) (z : ℝ) : ℝ :=
  let ν := (gaussianReal 0 1).tilted (fun u => ζ * F (z + Real.sqrt v * u))
  (∫ u, B (z + Real.sqrt v * u) * ((1 / (2 * Real.sqrt v)) * u) ∂ν) +
    ζ * ((∫ u, A (z + Real.sqrt v * u) *
      (M (z + Real.sqrt v * u) * ((1 / (2 * Real.sqrt v)) * u)) ∂ν) -
      (∫ u, A (z + Real.sqrt v * u) ∂ν) *
        (∫ u, M (z + Real.sqrt v * u) * ((1 / (2 * Real.sqrt v)) * u) ∂ν))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticSlabCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform bounded potential for the actual finite-slab inverse-curvature
comparison. The cap depends on exponents, not on the variance parameter. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def magneticSlabPotentialCap (L : List (ℝ × ℝ≥0)) (ζ : ℝ) : ℝ :=
  magneticFourthRatioCap ((ζ, 0) :: L) + (magneticThirdRatioCap ((ζ, 0) :: L)) ^ 2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_FinitePushforwardEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite pushforward weights and their entropy averages. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def finitePushforwardWeights {X Y : Type*} [Fintype X] [DecidableEq Y]
    (f : X → Y) (p : X → ℝ) (y : Y) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x => f x = y), p x

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_ConsecutiveBlockPrior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Repeated identical cavity constraints admit every even permutation
of their blocks. No coordinate sign flip is introduced. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def consecutiveBlockSitePermutation {n K : ℕ} (p : Equiv.Perm (Fin K)) : Equiv.Perm (Fin (K*n)) :=
  finProdFinEquiv.permCongr (Equiv.prodCongrLeft (fun _ : Fin n => p))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_ConsecutiveGroupProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Repeating a finite field block multiplies each group size by the
number of repetitions and preserves its attainable magnetizations. -/
noncomputable section
open scoped BigOperators
namespace InvariantIsing

def consecutiveSiteGroup {n : ℕ} {A : Type*} (K : ℕ) (group : Fin n → A) : Fin (K*n) → A :=
  fun i => group (finProdFinEquiv.symm i).2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_OffsetBlockSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Even permutations of the repeated blocks preserve an arbitrary initial remainder. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

def offsetBlockSitePermutation {r n K : ℕ} (p : Equiv.Perm (Fin K)) :
    Equiv.Perm (Fin (r+K*n)) :=
  finSumFinEquiv.permCongr (Equiv.sumCongr (Equiv.refl (Fin r))
    (consecutiveBlockSitePermutation (n := n) p))

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

def spectralSpinWeight (m : ℕ) : Fin (m + 1) → ℝ := Fin.lastCases 0 (fun _ => 1)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralPartitionPaths
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

def spectralPartitionQuantileWeights (m : ℕ) : Fin (m + 1) → Fin (m + 1) → ℝ :=
  Fin.lastCases (spectralSpinWeight m) (fun a => Pi.single a.castSucc 1)

def spectralPartitionRelation (m : ℕ) : Fin (m + 1) → ℝ :=
  Fin.lastCases (-1) (fun _ => 1)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralLabelCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counts on arbitrary finite spectral labels and their deterministic relabeling. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology Classical BigOperators

namespace InvariantIsing

def spectralLabelCount {ι : Type*} {N : ℕ}
    (g : Fin N → ι) (a : ι) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => g i=a)).card

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldRefineMagnetization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact magnetization levels under a one-cut field refinement. -/

noncomputable section
open IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldSplitIndex {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2)) : Fin (n + 1) :=
  if hj : j.val ≤ i.val then ⟨j.val, by omega⟩ else ⟨j.val - 1, by omega⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightUpdate
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

def fieldHeightIncrement {n : ℕ} (r : Fin (n + 1) → ℝ) (j : Fin (n + 1)) : ℝ :=
  r j - if hj : j.val = 0 then 0 else r ⟨j.val - 1, by omega⟩

lemma fieldHeightIncrement_update {n : ℕ} (r : Fin (n + 1) → ℝ)
    (i j : Fin (n + 1)) (t : ℝ) :
    fieldHeightIncrement (Function.update r i (r i + t)) j =
      fieldHeightIncrement r j + if j = i then t else if j.val = i.val + 1 then -t else 0 := by
  classical
  by_cases hj : j.val = 0
  · have hn : j.val ≠ i.val + 1 := by omega
    simp only [fieldHeightIncrement, hj, dite_true, sub_zero]
    by_cases hji : j = i
    · simp [hji]
    · simp [hji]
  · have hp : (⟨j.val - 1, by omega⟩ : Fin (n + 1)) = i ↔ j.val = i.val + 1 := by
      constructor
      · intro he
        have hv := congrArg Fin.val he
        simp only at hv
        omega
      · intro he
        apply Fin.ext
        simp only
        omega
    simp only [fieldHeightIncrement, hj, dite_false, Function.update_apply, hp]
    by_cases he : j = i
    · subst j
      have hn : i.val ≠ i.val + 1 := by omega
      simp only [ite_true, if_true, hn, ite_false, if_false]
      ring
    · by_cases hn : j.val = i.val + 1
      · have hpi : (⟨j.val - 1, by omega⟩ : Fin (n + 1)) = i := hp.mpr hn
        rw [hpi]
        simp only [he, hn, ite_false, if_false, ite_true, if_true]
        ring
      · simp [he, hn]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightJoint
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

def fieldHeightSlope {n : ℕ} (j : Fin (n + 1)) (i : Fin (n + 1)) : ℝ :=
  (if i = j then 1 else 0) -
    if hj : j.val = 0 then 0 else if i = (⟨j.val - 1, by omega⟩ : Fin (n + 1)) then 1 else 0

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The strict finite field-height cone and its original FieldStep
representatives. Positive increments give every height and order constraint. -/

noncomputable section
open IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

def fieldStrictHeightCone (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {r | ∀ j, 0 < fieldHeightIncrement r j}

lemma fieldHeightIncrement_succ {n : ℕ} (r : Fin (n + 1) → ℝ) (j : Fin n) :
    fieldHeightIncrement r j.succ = r j.succ - r j.castSucc := by
  unfold fieldHeightIncrement
  simp only [Fin.val_succ, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceDIte,
    Nat.add_sub_cancel]
  rfl

lemma fieldStrictHeightCone_strictMono {n : ℕ} {r : Fin (n + 1) → ℝ}
    (hr : r ∈ fieldStrictHeightCone n) : StrictMono r := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro j
  have h := hr j.succ
  rw [fieldHeightIncrement_succ] at h
  linarith

lemma fieldStrictHeightCone_nonneg {n : ℕ} {r : Fin (n + 1) → ℝ}
    (hr : r ∈ fieldStrictHeightCone n) (j : Fin (n + 1)) : 0 ≤ r j := by
  have h0 : 0 < r 0 := by simpa [fieldHeightIncrement] using hr 0
  exact h0.le.trans ((fieldStrictHeightCone_strictMono hr).monotone (Fin.zero_le j))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A convex increment box carrying one joint derivative family for two
strict field-height vectors and the segment joining them. -/

noncomputable section
open IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

def fieldHeightBox (n : ℕ) (m V : ℝ) : Set (Fin (n + 1) → ℝ) :=
  {r | ∀ j, fieldHeightIncrement r j ∈ Ioo m V}

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSquarePrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Composition of an earlier conditional spin square with an unchanged
later scalar recursion. This keeps the ordinary Gaussian root separate. -/

noncomputable section
open IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldPrefixIndex (P S : List (ℝ × ℝ≥0)) (i : Fin (P.length + 1)) :
    Fin ((P ++ S).length + 1) :=
  ⟨i.val, by simp only [List.length_append]; omega⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldScalarScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Change of position units for the actual finite conditional spin
chain. The spin observable acquires no multiplicative derivative factor. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldScaleIncrements (c : ℝ≥0) (L : List (ℝ × ℝ≥0)) : List (ℝ × ℝ≥0) :=
  L.map (fun av => (av.1, c ^ 2 * av.2))

lemma fieldScaleIncrements_length (c : ℝ≥0) (L : List (ℝ × ℝ≥0)) :
    (fieldScaleIncrements c L).length = L.length := by
  simp only [fieldScaleIncrements, List.length_map]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldRadialCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Radial monotonicity of the actual finite-field overlap levels. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldScaleCovariance (h : FieldStep) (c : ℝ≥0) : FieldStep where
  depth := h.depth
  cut := h.cut
  ordered_cut := h.ordered_cut
  first := h.first
  last := h.last
  height := fun i => (c : ℝ) ^ 2 * h.height i
  nonneg := fun i => mul_nonneg (sq_nonneg _) (h.nonneg i)
  ordered_height := fun _i _j hij => mul_le_mul_of_nonneg_left (h.ordered_height hij) (sq_nonneg _)

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

def fieldVaryingCap {E : Type*} (L : List (ℝ × (E → ℝ≥0))) (V : ℝ) : ℝ :=
  (L.map (fun av => av.1 * V / 2 + Real.log 2 / av.1)).sum

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightRegularization
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

def fieldHeightEpsilon (t : ℝ) : ℝ := max 0 (min t 1)

lemma fieldHeightEpsilon_nonneg (t : ℝ) : 0 ≤ fieldHeightEpsilon t := le_max_left _ _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_PositiveRationalApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive rational approximations to a finite probability vector,
with explicit integer multiplicities. -/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace InvariantIsing

def positiveApproxCount (x : ℝ) (k : ℕ) : ℕ := ⌊(k+1 : ℝ)*x⌋₊+1

def positiveApproxDenominator {m : ℕ} (ρ : Fin m → ℝ) (k : ℕ) : ℕ :=
  ∑ a, positiveApproxCount (ρ a) k

def positiveApproxWeights {m : ℕ} (ρ : Fin m → ℝ) (k : ℕ) (a : Fin m) : ℝ :=
  (positiveApproxCount (ρ a) k : ℝ)/positiveApproxDenominator ρ k

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralClipping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Clipping the finite spectra to the limiting support interval. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology Classical

namespace InvariantIsing

def spectralClip (a b x : ℝ) : ℝ := max a (min b x)

lemma continuous_spectralClip (a b : ℝ) : Continuous (spectralClip a b) :=
  continuous_const.max (continuous_const.min continuous_id)

lemma spectralClip_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) : spectralClip a b x∈Icc a b :=
  ⟨le_max_left _ _,max_le hab (min_le_left _ _)⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_OffsetFieldPopulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero-field prefix has vanishing population; repeated field blocks
retain the original label proportions. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace InvariantIsing

def offsetSiteGroup {n : ℕ} {A : Type*} (r K : ℕ) (g : Fin n → A) :
    Fin (r+K*n) → Option A :=
  Fin.addCases (fun _ => none) (fun i => some (consecutiveSiteGroup K g i))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_FiniteGaussianMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Gaussian maxima and their log-sum-exp approximation. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing
variable {X : Type*} [Fintype X] [Nonempty X]

def finiteGaussianMaximum {d : ℕ} (C : X → Fin d → ℝ) (g : Fin d → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun x => linearGaussian C g x)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_DenseFiniteMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Increasing finite maxima exhaust a continuous function on a dense sequence. -/
noncomputable section
open Filter Set
open scoped Topology
namespace InvariantIsing

def prefixMaximum (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i : Fin (n+1) => f i)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_DenseFiniteMinimum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Decreasing finite minima exhaust continuous functions on a dense sequence. -/
noncomputable section
open Filter Set
open scoped Topology
namespace InvariantIsing

def prefixMinimum (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i : Fin (n+1) => f i)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_FiniteFieldAtomMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Atom masses of a finitely supported external-field law, allowing
several labels to describe the same field value. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace InvariantIsing

def fieldAtomMass {A : Type*} [Fintype A] (γ c : A → ℝ) (x : ℝ) : ℝ :=
  ∑ a, if c a=x then γ a else 0

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_FiniteFieldLawCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two positive finite representations of the same field law have a
coupling supported on identical field values. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace InvariantIsing

def sameFieldCoupling {A B : Type*} [Fintype A]
    (γ c : A → ℝ) (δ d : B → ℝ) (a : A) (j : B) : ℝ :=
  if c a=d j then γ a*δ j/fieldAtomMass γ c (c a) else 0

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_FiniteFieldMatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Match as many sites of each field label as both finite populations contain. -/
noncomputable section
open scoped BigOperators
namespace InvariantIsing

def fieldLabelInjection {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (g : Fin N → A) (s : A → ℕ) (hs : ∀ a, s a ≤ spinGroupSize g a) :
    (Σ a, Fin (s a)) ↪ Fin N where
  toFun x := ((Fintype.equivFin {i : Fin N // g i=x.1}).symm
    (Fin.castLE (by simpa only [spinGroupSize, Fintype.card_subtype] using hs x.1) x.2)).val
  inj' := by
    rintro ⟨a,i⟩ ⟨b,j⟩ he
    have ha : g ((Fintype.equivFin {i : Fin N // g i=a}).symm
        (Fin.castLE (by simpa only [spinGroupSize, Fintype.card_subtype] using hs a) i)).val=a :=
      ((Fintype.equivFin {i : Fin N // g i=a}).symm
        (Fin.castLE (by simpa only [spinGroupSize, Fintype.card_subtype] using hs a) i)).property
    have hb : g ((Fintype.equivFin {i : Fin N // g i=b}).symm
        (Fin.castLE (by simpa only [spinGroupSize, Fintype.card_subtype] using hs b) j)).val=b :=
      ((Fintype.equivFin {i : Fin N // g i=b}).symm
        (Fin.castLE (by simpa only [spinGroupSize, Fintype.card_subtype] using hs b) j)).property
    have hab : a=b := ha.symm.trans ((congrArg g he).trans hb)
    subst b
    have hh := (Fintype.equivFin {i : Fin N // g i=a}).symm.injective (Subtype.ext he)
    have hij : i=j := by
      apply Fin.ext
      exact congrArg (fun z : Fin (Fintype.card {i : Fin N // g i=a}) => z.val) hh
    subst j
    rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_FiniteIndexDistribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive part of a finite random label has the same distribution. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Classical
namespace InvariantIsing

variable {Ω A : Type*} [MeasurableSpace Ω] [Fintype A]
  [MeasurableSpace A] [MeasurableSingletonClass A]

lemma finiteIndexWeight_sum (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → A) (hg : Measurable g) : ∑ a, finiteIndexWeight P g a=1 := by
  have hh := sum_measureReal_preimage_singleton (μ := P) Finset.univ
    (f := g) (fun a _ => hg (measurableSet_singleton a))
  simpa only [finiteIndexWeight,Finset.coe_univ,preimage_univ,probReal_univ] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_FiniteIndexCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint finite random labels give exact nonnegative transport plans. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace InvariantIsing

variable {Ω A B : Type*} [MeasurableSpace Ω] [Fintype A] [Fintype B]
  [MeasurableSpace A] [MeasurableSingletonClass A]
  [MeasurableSpace B] [MeasurableSingletonClass B]

def finiteIndexCoupling (P : Measure Ω) (g : Ω → A) (h : Ω → B) (a : A) (b : B) : ℝ :=
  P.real ((g ⁻¹' {a}) ∩ (h ⁻¹' {b}))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GordonWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two finite Gibbs levels in the Gaussian minimum--maximum comparison. -/
noncomputable section
open IsingPerceptron
open scoped BigOperators
namespace InvariantIsing
variable {U V : Type*} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]

def gordonRow (H : U × V → ℝ) (v : V) : ℝ :=
  Real.log (finitePartition (fun _ : U => 1) (fun u => H (u,v)))

def gordonValue (H : U × V → ℝ) : ℝ :=
  -Real.log (finitePartition (fun _ : V => 1) (fun v => -gordonRow H v))

def gordonInner (H : U × V → ℝ) (u : U) (v : V) : ℝ :=
  finiteGibbs (fun _ : U => 1) (fun u => H (u,v)) u

def gordonOuter (H : U × V → ℝ) (v : V) : ℝ :=
  finiteGibbs (fun _ : V => 1) (fun v => -gordonRow H v) v

def gordonWeight (H : U × V → ℝ) (x : U × V) : ℝ :=
  gordonOuter H x.2*gordonInner H x.1 x.2

def gordonRowMean (H D : U × V → ℝ) (v : V) : ℝ :=
  ∑ u, gordonInner H u v*D (u,v)

def gordonMean (H D : U × V → ℝ) : ℝ :=
  ∑ v, gordonOuter H v*gordonRowMean H D v

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_FiniteMinmax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite minimum--maximum values and their two-level log-sum-exp bounds. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing
variable {U V : Type*} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]

def finiteRowMax (H : U × V → ℝ) (v : V) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun u => H (u,v))

def finiteMinmax (H : U × V → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (finiteRowMax H)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticVariational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prescribed-magnetization variational expression in (7.3)--(7.4).
One common covariance path is used for every field group. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

instance instInhabitedRationalMagnetization {A : Type*} : Inhabited (RationalMagnetization A) :=
  ⟨⟨fun _ => 0, by intro a; norm_num⟩⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticPopulationCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transporting a magnetization profile through a finite coupling of
field populations increases its grouped constrained entropy. -/
noncomputable section
open Set
open scoped BigOperators
namespace InvariantIsing

def transportedMagnetization {A B : Type*} [Fintype A]
    (w : A → B → ℝ) (δ : B → ℝ) (mag : A → ℝ) (b : B) : ℝ :=
  (∑ a, w a b*mag a)/δ b

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_FinitePopulationCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A coupling retains a common fraction of every population and sends
the remaining mass independently to the required residual population. -/
noncomputable section
open scoped BigOperators
namespace InvariantIsing

def retainedPopulationCoupling {A : Type*} [DecidableEq A]
    (γ δ : A → ℝ) (ε : ℝ) (a j : A) : ℝ :=
  (if a=j then (1-ε)*γ a else 0)+γ a*(δ j-(1-ε)*γ j)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_KernelRelativeEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The conditional entropy identity needed for the finite Gaussian
sampling path. Its nonnegative integral form also covers zero variances. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace InvariantIsing

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace.CountableOrCountablyGenerated X Y]

/-- A measurable version of conditional relative entropy, for dominated kernels. -/
def kernelRelativeEntropy (κ η : Kernel X Y) [IsMarkovKernel κ] [IsMarkovKernel η]
    (x : X) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (klFun ((κ.rnDeriv η x y).toReal)) ∂η x

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

lemma measurable_simpleFieldIndex (s : SimpleFunc Ω ℝ) : Measurable (simpleFieldIndex s) :=
  s.measurable.subtype_mk

lemma simpleFieldWeight_sum (P : Measure Ω) [IsProbabilityMeasure P] (s : SimpleFunc Ω ℝ) :
    ∑ i, simpleFieldWeight P s i=1 :=
  finiteIndexWeight_sum P _ (measurable_simpleFieldIndex s)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The excess of the absolute field above a cutoff is a one-Lipschitz tail test. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace InvariantIsing

def fieldTail (M x : ℝ) : ℝ := max (|x|-M) 0

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SeedPairRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite two-path recursion for the ancestor-dependent uniform seeds. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing
variable {ι : Type}

def seedPairPathMean : (n : ℕ) → (ℕ → (ι → ℝ) → unitInterval → (ι → ℝ)) →
    ℕ → (ι → ℝ) → (ι → ℝ) → ((Fin n → (ι → ℝ) × (ι → ℝ)) → ℝ) → ℝ
  | 0, _, _, _, _, F => F Fin.elim0
  | n+1, ψ, 0, z₁, z₂, F =>
      ∫ u : unitInterval × unitInterval,
        seedPairPathMean n (fun i => ψ (i+1)) 0
          (z₁+ψ 0 z₁ u.1) (z₂+ψ 0 z₂ u.2)
          (fun w => F (Fin.cons (ψ 0 z₁ u.1,ψ 0 z₂ u.2) w)) ∂volume.prod volume
  | n+1, ψ, d+1, z₁, z₂, F =>
      ∫ u : unitInterval,
        seedPairPathMean n (fun i => ψ (i+1)) d
          (z₁+ψ 0 z₁ u) (z₂+ψ 0 z₂ u)
          (fun w => F (Fin.cons (ψ 0 z₁ u,ψ 0 z₂ u) w))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_MarkPairRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite conditional-mark recursion needed by the tensor and scalar terminals. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing
variable {ι : Type}

def markPairPathMean : (n : ℕ) → (ℕ → Kernel (ι → ℝ) (ι → ℝ)) →
    ℕ → (ι → ℝ) → (ι → ℝ) → ((Fin n → (ι → ℝ) × (ι → ℝ)) → ℝ) → ℝ
  | 0, _, _, _, _, F => F Fin.elim0
  | n+1, κ, 0, z₁, z₂, F =>
      ∫ a₁, ∫ a₂,
        markPairPathMean n (fun i => κ (i+1)) 0 (z₁+a₁) (z₂+a₂)
          (fun w => F (Fin.cons (a₁,a₂) w)) ∂κ 0 z₂ ∂κ 0 z₁
  | n+1, κ, d+1, z₁, z₂, F =>
      ∫ a, markPairPathMean n (fun i => κ (i+1)) d (z₁+a) (z₂+a)
        (fun w => F (Fin.cons (a,a) w)) ∂κ 0 z₁

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_MarkEndpointKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint kernels of the finite ancestor-dependent increment chain. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace InvariantIsing
variable {N : ℕ}

def markStateKernel (κ : Kernel (Fin N → ℝ) (Fin N → ℝ)) :
    Kernel (Fin N → ℝ) (Fin N → ℝ) :=
  (Kernel.id ×ₖ κ).map (fun p => p.1+p.2)

instance markStateKernel_markov (κ : Kernel (Fin N → ℝ) (Fin N → ℝ))
    [IsMarkovKernel κ] : IsMarkovKernel (markStateKernel κ) := by
  unfold markStateKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_fst.add measurable_snd)

def markTailEndpointKernel : ℕ → (ℕ → Kernel (Fin N → ℝ) (Fin N → ℝ)) →
    Kernel (Fin N → ℝ) (Fin N → ℝ)
  | 0, _ => Kernel.id
  | n+1, κ => markTailEndpointKernel n (fun i => κ (i+1)) ∘ₖ markStateKernel (κ 0)

instance markTailEndpointKernel_markov (n : ℕ)
    (κ : ℕ → Kernel (Fin N → ℝ) (Fin N → ℝ)) [∀ i, IsMarkovKernel (κ i)] :
    IsMarkovKernel (markTailEndpointKernel n κ) := by
  induction n generalizing κ with
  | zero => exact inferInstanceAs (IsMarkovKernel Kernel.id)
  | succ n ih =>
    let := ih (fun i => κ (i+1))
    change IsMarkovKernel (_ ∘ₖ _)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def markPairEndpointKernel : (n : ℕ) → (ℕ → Kernel (Fin N → ℝ) (Fin N → ℝ)) →
    Fin (n+1) → Kernel (Fin N → ℝ) ((Fin N → ℝ) × (Fin N → ℝ))
  | 0, _, _ => Kernel.id ×ₖ Kernel.id
  | n+1, κ, d => Fin.cases (markTailEndpointKernel (n+1) κ ×ₖ markTailEndpointKernel (n+1) κ)
      (fun j => markPairEndpointKernel n (fun i => κ (i+1)) j ∘ₖ markStateKernel (κ 0)) d

instance markPairEndpointKernel_markov (n : ℕ)
    (κ : ℕ → Kernel (Fin N → ℝ) (Fin N → ℝ)) [∀ i, IsMarkovKernel (κ i)]
    (d : Fin (n+1)) : IsMarkovKernel (markPairEndpointKernel n κ d) := by
  induction n generalizing κ with
  | zero => exact inferInstanceAs (IsMarkovKernel (Kernel.id ×ₖ Kernel.id))
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) d
    · change IsMarkovKernel (_ ×ₖ _)
      first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
    · let := ih (fun i => κ (i+1)) j
      change IsMarkovKernel (_ ∘ₖ _)
      first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_MarkEndpointIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded endpoint observables of independent and shared ancestor paths. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace InvariantIsing
variable {N : ℕ}

def markPairEndpoint (n : ℕ) (z₁ z₂ : Fin N → ℝ)
    (w : Fin n → (Fin N → ℝ) × (Fin N → ℝ)) :=
  (z₁ + ∑ i, (w i).1, z₂ + ∑ i, (w i).2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PoissonLabeledWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive rescaling cannot merge active labeled Poisson points. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal ENNReal
namespace InvariantIsing

instance intensityComponents_noAtoms (b : ℝ) (m : ℕ) :
    NullSingletonClass (intensityComponents (powerIntensity b) m : Measure ℝ) where
  measure_singleton x := by
    apply le_antisymm ?_ bot_le
    calc
      _ ≤ powerIntensity b {x} := sfiniteSeq_le _ _ _
      _ = 0 := measure_singleton x

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PositiveFieldApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive rational approximations to arbitrary finite field populations. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace InvariantIsing

def fieldApproxDenominator {A : Type*} [Fintype A] (γ : A → ℝ) (k : ℕ) : ℕ :=
  ∑ a, positiveApproxCount (γ a) k

def fieldApproxWeights {A : Type*} [Fintype A] (γ : A → ℝ) (k : ℕ) (a : A) : ℝ :=
  (positiveApproxCount (γ a) k : ℝ)/fieldApproxDenominator γ k

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticRoundedCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rounding an interior magnetization to an attainable spin count. -/
noncomputable section
open Filter
open scoped Topology
namespace InvariantIsing

def magneticRoundedCount (G : ℕ) (s : ℝ) : ℕ := ⌊(G:ℝ)*((1+s)/2)⌋₊

def magneticRoundedValue (G : ℕ) (s : ℝ) : ℝ :=
  if G=0 then s else 2*(magneticRoundedCount G s : ℝ)/G-1

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinCountMagnetization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real magnetization associated with an attainable integer count. -/
noncomputable section
namespace InvariantIsing

def spinCountMagnetization (G k : ℕ) : ℝ := if G=0 then 0 else 2*(k:ℝ)/G-1

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

def vectorTerminalUpdate (N n : ℕ) : ℕ → (Fin N → ℝ) × (Fin N → ℝ) → (Fin N → ℝ) :=
  stoppedUpdate n (fun _ p => p.1+p.2)

lemma measurable_vectorTerminalUpdate (N n i : ℕ) : Measurable (vectorTerminalUpdate N n i) :=
  measurable_stoppedUpdate n (fun _ => measurable_fst.add measurable_snd) i

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_VectorTerminalNoise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Terminal Gibbs sampling and retained trees for finite vector fields. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal ENNReal
namespace InvariantIsing

def vectorLeafSum (N : ℕ) : (n : ℕ) → (Fin N → ℝ) → NoiseLeaf (Fin N → ℝ) n → (Fin N → ℝ)
  | 0,z,_ => z
  | n+1,z,w => vectorLeafSum N n (z+w.2.1) w.2.2

lemma measurable_vectorLeafSum (N n : ℕ) :
    Measurable (fun p : (Fin N → ℝ) × NoiseLeaf (Fin N → ℝ) n => vectorLeafSum N n p.1 p.2) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih => exact ih.comp ((measurable_fst.add measurable_snd.snd.fst).prodMk measurable_snd.snd.snd)

def vectorTerminalNoiseLaw (N n : ℕ) (F : (Fin N → ℝ) → ℝ)
    (z : Fin N → ℝ) (T : NoiseTree (Fin N → ℝ) n) : Measure (NoiseLeaf (Fin N → ℝ) n) :=
  normalizeMass ((noiseLeafKernel (Fin N → ℝ) n T).withDensity
    (fun w => ENNReal.ofReal (Real.exp (F (vectorLeafSum N n z w)))))

instance vectorTerminalNoiseLaw_probability (N n : ℕ) (F : (Fin N → ℝ) → ℝ)
    (z : Fin N → ℝ) (T : NoiseTree (Fin N → ℝ) n) :
    IsProbabilityMeasure (vectorTerminalNoiseLaw N n F z T) := normalizeMass_probability _

lemma measurable_vectorTerminalNoiseLaw (N n : ℕ) (F : (Fin N → ℝ) → ℝ) (hF : Measurable F)
    (z : Fin N → ℝ) : Measurable (vectorTerminalNoiseLaw N n F z) :=
  measurable_normalizeMass.comp ((measurable_withDensity_fixed
    ((hF.comp ((measurable_vectorLeafSum N n).comp (measurable_const.prodMk measurable_id))).exp.ennreal_ofReal)).comp
      (noiseLeafKernel (Fin N → ℝ) n).measurable)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianGramColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact column decomposition and the positive leave-one-column Gram matrix. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

def gaussianGramRawColumn {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m)) (j : Fin m) : Fin N → ℝ :=
  fun i => z (i,j)

def gaussianGramLeaveOneOut {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m))
    (j : Fin m) : Matrix (Fin N) (Fin N) ℝ :=
  (1/(N : ℝ)) • ∑ l ∈ Finset.univ.erase j, vecMulVec (gaussianGramRawColumn z l) (gaussianGramRawColumn z l)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianColumnProductLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical Gaussian matrix as independent Gaussian columns. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace InvariantIsing

def gaussianColumnArray {N m : ℕ} (g : Fin m → Fin N → ℝ) :
    EuclideanSpace ℝ (Fin N × Fin m) := WithLp.toLp 2 (fun p => g p.2 p.1)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianLeaveOneColumn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact leave-one-column identities at the physical Gaussian normalization. -/
noncomputable section
open Matrix
namespace InvariantIsing

def gaussianPatternScaledColumn {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m))
    (j : Fin m) : Fin N → ℝ := (Real.sqrt N)⁻¹ • gaussianGramRawColumn z j

def gaussianGramLeaveResolvent {N m : ℕ} (t : ℝ) (z : EuclideanSpace ℝ (Fin N × Fin m))
    (j : Fin m) : Matrix (Fin N) (Fin N) ℝ :=
  (t • (1 : Matrix (Fin N) (Fin N) ℝ)+gaussianGramLeaveOneOut z j)⁻¹

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianGramResolventEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact finite-dimensional leave-one-column equation for the physical Gram transform. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

def gaussianGramColumnQuadratic {N m : ℕ} (t : ℝ) (z : EuclideanSpace ℝ (Fin N × Fin m))
    (j : Fin m) : ℝ :=
  gaussianPatternScaledColumn z j ⬝ᵥ
    (gaussianGramLeaveResolvent t z j *ᵥ gaussianPatternScaledColumn z j)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianPatternEuclideanNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Euclidean operator norm of the physical Gaussian array is 1-Lipschitz. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
namespace InvariantIsing

def gaussianPatternEuclideanOperator {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
  (gaussianPatternArray z).toEuclideanLin.toContinuousLinearMap

def gaussianPatternSingularMax {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m)) : ℝ :=
  ‖gaussianPatternEuclideanOperator z‖

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianPatternSingularMinimum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The least singular value, as an actual unit-sphere minimum, is 1-Lipschitz. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology
namespace InvariantIsing

def gaussianPatternSingularMin {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m)) : ℝ :=
  ⨅ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1, ‖gaussianPatternEuclideanOperator z x‖

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianSmoothing
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized smoothing preserves the precise scalar Lipschitz constant. -/
noncomputable section
open MeasureTheory ContinuousLinearMap
open scoped NNReal Convolution ContDiff
namespace InvariantIsing

def gaussianSmooth {d : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  φ.normed volume ⋆[lsmul ℝ ℝ, volume] f

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.KLS_Model
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace LeanBlast.KLS

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

def expectation {n : ℕ} (μ : Measure (Space n)) (f : Space n → ℝ) : ℝ :=
  ∫ x, f x ∂μ

def variance {n : ℕ} (μ : Measure (Space n)) (f : Space n → ℝ) : ℝ :=
  ∫ x, (f x - expectation μ f) ^ 2 ∂μ

def dirichletEnergy {n : ℕ} (μ : Measure (Space n)) (f : Space n → ℝ) : ℝ :=
  ∫ x, ‖gradient f x‖ ^ 2 ∂μ

/-- The exact compactly supported smooth real test-function class. -/
def IsTestFunction {n : ℕ} (f : Space n → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ258_II.KLS_Measures_PotentialMeasure
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff

namespace LeanBlast.KLS

variable {n : ℕ}

def potentialPartition (V : Space n → ℝ) : ℝ :=
  ∫ x, Real.exp (-V x)

def potentialMeasure (V : Space n → ℝ) : Measure (Space n) :=
  volume.tilted (fun x => -V x)

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ258_II.KLS_Stein_SteinHessianDefs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Matrix
open scoped BigOperators ContDiff

namespace LeanBlast.KLS

def standardBasisVector {n : ℕ} (i : Fin n) : Space n :=
  EuclideanSpace.basisFun (Fin n) ℝ i

def hessianMatrix {n : ℕ} (f : Space n → ℝ) (x : Space n) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => fderiv ℝ (fderiv ℝ f) x (standardBasisVector i) (standardBasisVector j)

def steinGamma {n : ℕ} (ψ g h : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ a, ∑ b, gradient g x a * (hessianMatrix ψ x)⁻¹ a b * gradient h x b

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ258_II.KLS_Regularization_RegularPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace LeanBlast.KLS

structure IsRegularPotential {n : ℕ} (V : Space n → ℝ) (t t' : ℝ) : Prop where
  contDiff : ContDiff ℝ ∞ V
  lower_pos : 0 < t
  le_upper : t ≤ t'
  lower_bound : ∀ x v : Space n,
    t * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v
  upper_bound : ∀ x v : Space n,
    fderiv ℝ (fderiv ℝ V) x v v ≤ t' * ‖v‖ ^ 2

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ258_II.KLS_Spectral_BrascampLiebMoments
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace LeanBlast.KLS

def blWeight (t a b : ℝ) : ℝ := Real.exp (-t * a - t ^ 2 / 2 * b)

def blWeightDeriv (t a b : ℝ) : ℝ := (-a - t * b) * blWeight t a b

def blWeightSecond (t a b : ℝ) : ℝ := ((a + t * b) ^ 2 - b) * blWeight t a b

section Moments

variable {n : ℕ} (μ : Measure (Space n)) [IsProbabilityMeasure μ]
  (h q : Space n → ℝ)

def blMoment (t : ℝ) : ℝ := ∫ x, blWeight t (h x) (q x) ∂μ
def blMomentDeriv (t : ℝ) : ℝ := ∫ x, blWeightDeriv t (h x) (q x) ∂μ
def blMomentSecond (t : ℝ) : ℝ := ∫ x, blWeightSecond t (h x) (q x) ∂μ
def blLogMoment (t : ℝ) : ℝ := Real.log (blMoment μ h q t)

@[simp] theorem blMoment_zero : blMoment μ h q 0 = 1 := by
  simp [blMoment, blWeight]

omit [IsProbabilityMeasure μ] in
@[simp] theorem blMomentDeriv_zero : blMomentDeriv μ h q 0 = -(∫ x, h x ∂μ) := by
  simp [blMomentDeriv, blWeightDeriv, blWeight, integral_neg]

end Moments

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ258_II.KLS_Spectral_BrascampLiebPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Matrix
open scoped BigOperators ContDiff Topology Matrix.Norms.Elementwise

namespace LeanBlast.KLS

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (V h q : E → ℝ)

def blPerturbation (p : ℝ × E) : ℝ := V p.2 + p.1 * h p.2 + p.1 ^ 2 / 2 * q p.2

end Calculus

end LeanBlast.KLS

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianQuadraticPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-dimensional quadratic potential for Gaussian Poincare. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace InvariantIsing

def gaussianQuadraticPotential {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1/2 : ℝ)*‖x‖^2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianCompactVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extending Gaussian Poincare from smooth to compact Lipschitz tests. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace InvariantIsing

def gaussianApproxBump (d n : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) where
  rIn := (1/(n+1 : ℝ))/2
  rOut := 1/(n+1 : ℝ)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : 0 < 1/(n+1 : ℝ) := by positivity
    linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianConeCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact scalar cutoffs preserving the exact Lipschitz constant. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace InvariantIsing

def gaussianCone {d : ℕ} (L : ℝ≥0) (R : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  max ((L : ℝ)*(R-‖x‖)) 0

def gaussianConeCutoff {d : ℕ} (L : ℝ≥0) (R : ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  max (-gaussianCone L R x) (min (f x) (gaussianCone L R x))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianCoordinateNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact second moments and the square-root dimension bound for coordinate Gaussian norms. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace InvariantIsing
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def gaussianCoordinateVector (e : κ → ι) (g : ι → ℝ) : EuclideanSpace ℝ κ :=
  WithLp.toLp 2 (fun j => g (e j))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianDiagonalQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact mean and variance of a diagonal Gaussian quadratic form. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace InvariantIsing

def gaussianDiagonalQuadratic {N : ℕ} (a : Fin N → ℝ) (g : Fin N → ℝ) : ℝ := ∑ i, a i*(g i)^2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_HermitianGaussianQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Gaussian quadratic mean and variance in finite dimension. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace
namespace InvariantIsing

def gaussianQuadraticForm {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (x : EuclideanSpace ℝ (Fin N)) : ℝ := ⟪x,A.toEuclideanLin x⟫

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_PositiveResolventSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral bounds for the positive resolvents occurring after deletion of a column. -/
noncomputable section
open Matrix
open scoped BigOperators RealInnerProductSpace
namespace InvariantIsing

def positiveResolvent {N : ℕ} (t : ℝ) (B : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  (t • (1 : Matrix (Fin N) (Fin N) ℝ)+B)⁻¹

lemma positiveResolvent_posDef {N : ℕ} {t : ℝ} (ht : 0 < t)
    {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.PosSemidef) : (positiveResolvent t B).PosDef :=
  ((Matrix.PosDef.one.smul ht).add_posSemidef hB).inv

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianColumnDeviation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrability of the actual leave-one-column quadratic deviation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
namespace InvariantIsing

def gaussianGramColumnDeviation {N m : ℕ} (t : ℝ) (z : EuclideanSpace ℝ (Fin N × Fin m))
    (j : Fin m) : ℝ := |gaussianGramColumnQuadratic t z j-(gaussianGramLeaveResolvent t z j).trace/N|

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianTranspose
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transposition preserves the actual standard Gaussian array law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
namespace InvariantIsing

def gaussianPatternTranspose (N m : ℕ) :
    EuclideanSpace ℝ (Fin N × Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m × Fin N) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.prodComm (Fin N) (Fin m))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_IndexedGaussianMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite maximum comparison with an arbitrary nonempty Gaussian coordinate set. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing
variable {X ι : Type*} [Fintype X] [Nonempty X] [Fintype ι]

def indexedGaussianMaximum (C : X → ι → ℝ) (g : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun x => ∑ i, C x i*g i)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticBlockError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite block error vanishes uniformly over field partitions with
bounded final height and magnetizations in a fixed interior interval. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators NNReal Topology

namespace InvariantIsing

def magneticUniformBiasBound (H r : ℝ) : ℝ := (Real.log 2 + H / 2) / (1 - r)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedKernelFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unrestricted member of the constrained sampling construction is
exactly the previously evaluated canonical scalar-field law. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron
open scoped NNReal ENNReal BigOperators

namespace InvariantIsing

lemma finiteFieldIncrements_positive (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) :
    ∀ av ∈ List.ofFn (fun i : Fin n => (b i, v i)), 0 < av.1 := by
  intro av hav
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hav
  exact hb i i.isLt

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticScaledSlab
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal scaled inverse curvature used in the radial comparison.
Time is physical variance; its scaling yields the coefficient αζ. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma fieldScaleIncrements_positive (c : ℝ≥0) (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) :
    ∀ av ∈ fieldScaleIncrements c L, 0 < av.1 := by
  intro av hav
  obtain ⟨bv, hb, rfl⟩ := List.mem_map.mp hav
  exact hL bv hb

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticAdjacentCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moving a nonnegative variance increment from a larger exponent to the
preceding smaller exponent decreases the actual inverse curvature. -/

noncomputable section
open Filter Set IsingPerceptron
open scoped NNReal Topology

namespace InvariantIsing

lemma positive_cons {a : ℝ} (ha : 0 < a) (v : ℝ≥0)
    {L : List (ℝ × ℝ≥0)} (hL : ∀ av ∈ L, 0 < av.1) :
    ∀ av ∈ (a, v) :: L, 0 < av.1 := by
  intro av hav
  rcases List.mem_cons.mp hav with rfl | hav
  · exact ha
  · exact hL av hav

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticPrefixComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common finite prefix preserves inverse-curvature order and the
associated conditional-square order up to the end of that prefix. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma positive_append (P L : List (ℝ × ℝ≥0))
    (hP : ∀ av ∈ P, 0 < av.1) (hL : ∀ av ∈ L, 0 < av.1) :
    ∀ av ∈ P ++ L, 0 < av.1 := by
  intro av hav
  rcases List.mem_append.mp hav with hp | hl
  · exact hP av hp
  · exact hL av hl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_MPEdgeArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact centre, radius, and critical-edge arithmetic for the displayed MP density. -/
noncomputable section
namespace InvariantIsing

lemma mp_edge_centre_radius {α : ℝ} (hα : 0 ≤ α) :
    marchenkoPasturA α = 1+α-2*Real.sqrt α ∧
    marchenkoPasturB α = 1+α+2*Real.sqrt α := by
  have hs := Real.sq_sqrt hα
  constructor
  · unfold marchenkoPasturA
    nlinarith
  · unfold marchenkoPasturB
    nlinarith

lemma mp_radius_positive {α : ℝ} (hα : 0 < α) : 0 < 2*Real.sqrt α := by positivity

lemma mp_centre_exceeds_radius {α : ℝ} (hα : 0 ≤ α) (hne : α ≠ 1) :
    |2*Real.sqrt α| < 1+α := by
  have hs := Real.sq_sqrt hα
  have hne' : Real.sqrt α ≠ 1 := by intro h; rw [h] at hs; norm_num at hs; exact hne hs.symm
  have hp := sq_pos_of_ne_zero (sub_ne_zero.mpr hne')
  rw [abs_of_nonneg (by positivity)]
  nlinarith

lemma mp_centre_radius_discriminant {α : ℝ} (hα : 0 ≤ α) :
    (1+α)^2-(2*Real.sqrt α)^2 = (α-1)^2 := by
  have hs := Real.sq_sqrt hα
  nlinarith

lemma mp_centre_radius_sqrt {α : ℝ} (hα : 0 ≤ α) :
    Real.sqrt ((1+α)^2-(2*Real.sqrt α)^2) = |α-1| := by
  rw [mp_centre_radius_discriminant hα,Real.sqrt_sq_eq_abs]

lemma mp_continuous_mass (α : ℝ) : (1+α-|α-1|)/2 = min 1 α := by
  rcases le_total α 1 with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h),min_eq_right h]
    ring
  · rw [abs_of_nonneg (sub_nonneg.mpr h),min_eq_left h]
    ring

lemma mp_total_mass (α : ℝ) : max (1-α) 0+min 1 α = 1 := by
  rcases le_total α 1 with h | h
  · rw [max_eq_left (sub_nonneg.mpr h),min_eq_right h]
    ring
  · rw [max_eq_right (sub_nonpos.mpr h),min_eq_left h]
    simp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_MPTrigonometricDenominator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary positive-denominator identities for the MP density integral. -/
noncomputable section
open Real Set
namespace InvariantIsing

lemma mp_cos_denominator_pos {a b : ℝ} (hab : |b| < a) (x : ℝ) : 0 < a+b*cos x := by
  have hbc : |b*cos x| ≤ |b| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg b) (abs_cos_le_one x)
  have h := neg_abs_le (b*cos x)
  linarith

lemma mp_discriminant_pos {a b : ℝ} (hab : |b| < a) : 0 < a^2-b^2 := by
  have ha : 0 < a := lt_of_le_of_lt (abs_nonneg b) hab
  have hs := (sq_lt_sq₀ (abs_nonneg b) ha.le).mpr hab
  rw [sq_abs] at hs
  linarith

lemma mp_cos_fraction_identity {a b : ℝ} (hab : |b| < a) (x : ℝ) :
    1-((a*cos x+b)/(a+b*cos x))^2 =
      (a^2-b^2)*(sin x)^2/(a+b*cos x)^2 := by
  have hd := (mp_cos_denominator_pos hab x).ne'
  apply (eq_div_iff (pow_ne_zero 2 hd)).mpr
  rw [div_pow,sub_mul,one_mul,div_mul_cancel₀ _ (pow_ne_zero 2 hd)]
  linear_combination -(a^2-b^2)*(sin_sq_add_cos_sq x)

lemma mp_cos_fraction_mem_Ioo {a b : ℝ} (hab : |b| < a) {x : ℝ} (hx : x ∈ Ioo 0 Real.pi) :
    (a*cos x+b)/(a+b*cos x) ∈ Ioo (-1) 1 := by
  have hi := mp_cos_fraction_identity hab x
  have hs := sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have hp : 0 < (a^2-b^2)*(sin x)^2/(a+b*cos x)^2 := by
    exact div_pos (mul_pos (mp_discriminant_pos hab) (sq_pos_of_pos hs))
      (sq_pos_of_pos (mp_cos_denominator_pos hab x))
  constructor <;> nlinarith

lemma mp_cos_fraction_hasDerivAt {a b : ℝ} (hab : |b| < a) (x : ℝ) :
    HasDerivAt (fun y => (a*cos y+b)/(a+b*cos y))
      (-(a^2-b^2)*sin x/(a+b*cos x)^2) x := by
  have h := (((hasDerivAt_cos x).const_mul a).add_const b).div
    ((hasDerivAt_cos x).const_mul b |>.const_add a) (mp_cos_denominator_pos hab x).ne'
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_MPTrigonometricPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An elementary antiderivative for the denominator in the MP density integral. -/
noncomputable section
open Real Set
namespace InvariantIsing

def mpAnglePrimitive (a b x : ℝ) : ℝ :=
  arccos ((a*cos x+b)/(a+b*cos x))/sqrt (a^2-b^2)

lemma mp_cos_fraction_sqrt {a b : ℝ} (hab : |b| < a) {x : ℝ} (hx : x ∈ Ioo 0 Real.pi) :
    sqrt (1-((a*cos x+b)/(a+b*cos x))^2) =
      sqrt (a^2-b^2)*sin x/(a+b*cos x) := by
  rw [mp_cos_fraction_identity hab x,
    sqrt_div (mul_nonneg (mp_discriminant_pos hab).le (sq_nonneg _)),
    sqrt_mul (mp_discriminant_pos hab).le,
    sqrt_sq (sin_pos_of_pos_of_lt_pi hx.1 hx.2).le,
    sqrt_sq (mp_cos_denominator_pos hab x).le]

lemma mpAnglePrimitive_hasDerivAt {a b : ℝ} (hab : |b| < a) {x : ℝ} (hx : x ∈ Ioo 0 Real.pi) :
    HasDerivAt (mpAnglePrimitive a b) (1/(a+b*cos x)) x := by
  have hm := mp_cos_fraction_mem_Ioo hab hx
  have hc := (hasDerivAt_arccos (ne_of_gt hm.1) (ne_of_lt hm.2)).comp x
    (mp_cos_fraction_hasDerivAt hab x)
  have hs := sqrt_pos.mpr (mp_discriminant_pos hab)
  have hd := mp_cos_denominator_pos hab x
  have hsin := sin_pos_of_pos_of_lt_pi hx.1 hx.2
  unfold mpAnglePrimitive
  have hc' := hc.div_const (sqrt (a^2-b^2))
  simp only [Function.comp_def] at hc'
  convert hc' using 1
  all_goals try with_reducible_and_instances rfl
  rw [mp_cos_fraction_sqrt hab hx]
  have hsq := sq_sqrt (mp_discriminant_pos hab).le
  field_simp [hs.ne',hd.ne',hsin.ne']
  nlinarith

lemma continuous_mpAnglePrimitive {a b : ℝ} (hab : |b| < a) :
    Continuous (mpAnglePrimitive a b) := by
  unfold mpAnglePrimitive
  apply Continuous.div_const
  apply continuous_arccos.comp
  exact ((continuous_const.mul continuous_cos).add continuous_const).div
    (continuous_const.add (continuous_const.mul continuous_cos))
    (fun x => (mp_cos_denominator_pos hab x).ne')

theorem mp_integral_cos_denominator {a b : ℝ} (hab : |b| < a) :
    (∫ x in (0 : ℝ)..Real.pi, 1/(a+b*cos x)) = Real.pi/sqrt (a^2-b^2) := by
  have hi : IntervalIntegrable (fun x : ℝ => 1/(a+b*cos x)) MeasureTheory.volume 0 Real.pi :=
    (continuous_const.div (continuous_const.add (continuous_const.mul continuous_cos))
      (fun x => (mp_cos_denominator_pos hab x).ne')).intervalIntegrable 0 Real.pi
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le pi_pos.le
    (continuous_mpAnglePrimitive hab).continuousOn (fun x hx => mpAnglePrimitive_hasDerivAt hab hx) hi
  have hp : a+b ≠ 0 := by simpa using (mp_cos_denominator_pos hab 0).ne'
  have hn : a-b ≠ 0 := by simpa only [cos_pi,mul_neg_one,sub_eq_add_neg] using (mp_cos_denominator_pos hab Real.pi).ne'
  have he : (a*(-1)+b)/(a+b*(-1)) = -1 := by
    apply (div_eq_iff (show a+b*(-1) ≠ 0 by simpa only [mul_neg_one,sub_eq_add_neg] using hn)).mpr
    ring
  simpa only [mpAnglePrimitive,cos_zero,cos_pi,mul_one,he,div_self hp,
    arccos_one,arccos_neg_one,zero_div,sub_zero] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_MPTrigonometricIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The elementary semicircle-over-resolvent integral needed by the MP density. -/
noncomputable section
open Real
namespace InvariantIsing

lemma mp_sine_fraction_identity {a b : ℝ} (hab : |b| < a) (hb : b ≠ 0) (x : ℝ) :
    (sin x)^2/(a+b*cos x) = a/b^2-cos x/b-
      ((a^2-b^2)/b^2)*(1/(a+b*cos x)) := by
  have hd := (mp_cos_denominator_pos hab x).ne'
  field_simp [hb,hd]
  linear_combination b^2*(sin_sq_add_cos_sq x)

theorem mp_integral_sine_fraction {a b : ℝ} (hab : |b| < a) (hb : b ≠ 0) :
    (∫ x in (0 : ℝ)..Real.pi, (sin x)^2/(a+b*cos x)) =
      Real.pi*(a-sqrt (a^2-b^2))/b^2 := by
  have hc : IntervalIntegrable (fun x : ℝ => cos x/b) MeasureTheory.volume 0 Real.pi :=
    (continuous_cos.div_const b).intervalIntegrable _ _
  have hi : IntervalIntegrable (fun x : ℝ => 1/(a+b*cos x)) MeasureTheory.volume 0 Real.pi :=
    (continuous_const.div (continuous_const.add (continuous_const.mul continuous_cos))
      (fun x => (mp_cos_denominator_pos hab x).ne')).intervalIntegrable _ _
  calc
    _ = ∫ x in (0 : ℝ)..Real.pi, a/b^2-cos x/b-((a^2-b^2)/b^2)*(1/(a+b*cos x)) := by
      apply intervalIntegral.integral_congr
      intro x _
      exact mp_sine_fraction_identity hab hb x
    _ = Real.pi*(a/b^2)-((a^2-b^2)/b^2)*(Real.pi/sqrt (a^2-b^2)) := by
      rw [intervalIntegral.integral_sub (intervalIntegrable_const.sub hc) (hi.const_mul _),
        intervalIntegral.integral_sub intervalIntegrable_const hc,
        intervalIntegral.integral_const,intervalIntegral.integral_div,
        integral_cos,intervalIntegral.integral_const_mul,mp_integral_cos_denominator hab]
      simp
    _ = _ := by
      have hs := sqrt_pos.mpr (mp_discriminant_pos hab)
      have hsq := sq_sqrt (mp_discriminant_pos hab).le
      field_simp [hb,hs.ne']
      nlinarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_MPTrigonometricCritical
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero-edge endpoint of the MP angular integral. -/
noncomputable section
open Real MeasureTheory
namespace InvariantIsing

lemma mp_critical_sine_fraction {b : ℝ} (hb : 0 < b) {x : ℝ}
    (hx : x ∈ Set.Ioo 0 Real.pi) :
    (sin x)^2/(b+b*cos x) = (1-cos x)/b := by
  have hc : -1 < cos x := by
    simpa only [cos_pi] using cos_lt_cos_of_nonneg_of_le_pi hx.1.le (le_refl Real.pi) hx.2
  have hd : b+b*cos x ≠ 0 := ne_of_gt (by nlinarith)
  apply (div_eq_div_iff hd hb.ne').mpr
  linear_combination b*(sin_sq_add_cos_sq x)

theorem mp_integral_sine_fraction_critical {b : ℝ} (hb : 0 < b) :
    (∫ x in (0 : ℝ)..Real.pi, (sin x)^2/(b+b*cos x)) = Real.pi/b := by
  have he : (∫ x in (0 : ℝ)..Real.pi, (sin x)^2/(b+b*cos x)) =
      ∫ x in (0 : ℝ)..Real.pi, (1-cos x)/b := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne Real.pi] with x hx
    intro hmem
    rw [Set.uIoc_of_le pi_pos.le] at hmem
    exact mp_critical_sine_fraction hb ⟨hmem.1,lt_of_le_of_ne hmem.2 hx⟩
  rw [he,intervalIntegral.integral_div,
    intervalIntegral.integral_sub intervalIntegrable_const (continuous_cos.intervalIntegrable 0 Real.pi),
    intervalIntegral.integral_const,integral_cos]
  simp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_MPAngularMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization of the continuous part of the MP law in angular coordinates. -/
noncomputable section
open Real
namespace InvariantIsing

theorem mp_angular_continuous_mass {α : ℝ} (hα : 0 < α) :
    (2*α/Real.pi)*(∫ x in (0 : ℝ)..Real.pi,
      (sin x)^2/(1+α+2*sqrt α*cos x)) = min 1 α := by
  by_cases he : α = 1
  · subst α
    have h := mp_integral_sine_fraction_critical (b := 2) (by norm_num)
    norm_num at h ⊢
    rw [h]
    field_simp
  · have hab := mp_centre_exceeds_radius hα.le he
    have hb := (mp_radius_positive hα).ne'
    rw [mp_integral_sine_fraction hab hb,mp_centre_radius_sqrt hα.le]
    have hs : (2*sqrt α)^2 = 4*α := by nlinarith [sq_sqrt hα.le]
    rw [hs]
    calc
      _ = (1+α-|α-1|)/2 := by field_simp; ring
      _ = _ := mp_continuous_mass α

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_MPAngularIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrability of the angular MP density, including the critical zero edge. -/
noncomputable section
open Real MeasureTheory
namespace InvariantIsing

lemma mp_critical_sine_integrable {b : ℝ} (hb : 0 < b) :
    IntervalIntegrable (fun x => (sin x)^2/(b+b*cos x)) volume 0 Real.pi := by
  apply (((continuous_const.sub continuous_cos).div_const b).intervalIntegrable 0 Real.pi).congr_uIoo
  intro x hx
  rw [Set.uIoo_of_le pi_pos.le] at hx
  exact (mp_critical_sine_fraction hb hx).symm

lemma mp_angular_sine_integrable {α : ℝ} (hα : 0 < α) :
    IntervalIntegrable (fun x => (sin x)^2/(1+α+2*sqrt α*cos x)) volume 0 Real.pi := by
  by_cases he : α = 1
  · subst α
    simpa only [sqrt_one,mul_one,show (1 : ℝ)+1=2 by norm_num] using
      mp_critical_sine_integrable (b := 2) (by norm_num)
  · exact ((continuous_sin.pow 2).div
      (continuous_const.add (continuous_const.mul continuous_cos))
      (fun x => (mp_cos_denominator_pos (mp_centre_exceeds_radius hα.le he) x).ne')).intervalIntegrable 0 Real.pi

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_MarchenkoPasturTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unique nonnegative solution of the real Marchenko--Pastur transform equation. -/
noncomputable section
namespace InvariantIsing

def marchenkoPasturTransform (t α : ℝ) : ℝ :=
  (-(t+α-1)+Real.sqrt ((t+α-1)^2+4*t))/(2*t)

def marchenkoPasturResidual (t α u : ℝ) : ℝ := 1-t*u-α*(u/(1+u))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_MPAngularCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact change of variables for the displayed Marchenko--Pastur density. -/
noncomputable section
open Real Set
namespace InvariantIsing

def mpDensity (α x : ℝ) : ℝ :=
  sqrt ((marchenkoPasturB α-x)*(x-marchenkoPasturA α))/(2*Real.pi*x)

def mpAngle (α x : ℝ) : ℝ := 1+α+2*sqrt α*cos x

lemma mpAngle_endpoints {α : ℝ} (hα : 0 ≤ α) :
    mpAngle α 0 = marchenkoPasturB α ∧ mpAngle α Real.pi = marchenkoPasturA α := by
  obtain ⟨ha,hb⟩ := mp_edge_centre_radius hα
  constructor
  · simp only [mpAngle,cos_zero,mul_one,hb]
  · simp only [mpAngle,cos_pi,mul_neg_one,ha,sub_eq_add_neg]

lemma mpAngle_hasDerivAt (α x : ℝ) :
    HasDerivAt (mpAngle α) (-(2*sqrt α)*sin x) x := by
  unfold mpAngle
  convert ((hasDerivAt_cos x).const_mul (2*sqrt α)).const_add (1+α) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [mul_neg, neg_mul]

lemma mpAngle_sqrt {α x : ℝ} (hα : 0 ≤ α) (hx : x ∈ Icc 0 Real.pi) :
    sqrt ((marchenkoPasturB α-mpAngle α x)*(mpAngle α x-marchenkoPasturA α)) =
      2*sqrt α*sin x := by
  obtain ⟨ha,hb⟩ := mp_edge_centre_radius hα
  have he : (marchenkoPasturB α-mpAngle α x)*(mpAngle α x-marchenkoPasturA α) =
      (2*sqrt α*sin x)^2 := by
    rw [ha,hb]
    unfold mpAngle
    linear_combination -(2*sqrt α)^2*(sin_sq_add_cos_sq x)
  rw [he,sqrt_sq]
  exact mul_nonneg (by positivity) (sin_nonneg_of_nonneg_of_le_pi hx.1 hx.2)

lemma mpAngle_density_jacobian {α x : ℝ} (hα : 0 ≤ α) (hx : x ∈ Icc 0 Real.pi) :
    (2*sqrt α*sin x)*mpDensity α (mpAngle α x) =
      (2*α/Real.pi)*((sin x)^2/mpAngle α x) := by
  unfold mpDensity
  rw [mpAngle_sqrt hα hx]
  ring_nf
  rw [sq_sqrt hα]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_MPDensitySubstitution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact real change of variables for the literal MP density on its support interval. -/
noncomputable section
open Real Set MeasureTheory
namespace InvariantIsing

lemma continuous_mpAngle (α : ℝ) : Continuous (mpAngle α) :=
  continuous_const.add (continuous_const.mul continuous_cos)

lemma mpAngle_deriv_nonpos {α x : ℝ} (hx : x ∈ Ioo 0 Real.pi) :
    -(2*sqrt α)*sin x ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg (by norm_num) (sqrt_nonneg _)))
    (sin_pos_of_pos_of_lt_pi hx.1 hx.2).le

theorem mpDensity_substitution {α : ℝ} (hα : 0 < α) (g : ℝ → ℝ) :
    (∫ y in Icc (marchenkoPasturA α) (marchenkoPasturB α), mpDensity α y*g y) =
      ∫ x in Icc 0 Real.pi, (2*α/Real.pi)*((sin x)^2/mpAngle α x)*g (mpAngle α x) := by
  have h := integral_Icc_deriv_smul_of_deriv_nonpos
    (f := mpAngle α) (f' := fun x => -(2*sqrt α)*sin x)
    (g := fun y => mpDensity α y*g y)
    (continuous_mpAngle α).continuousOn (fun x _ => mpAngle_hasDerivAt α x)
    (fun _ hx => mpAngle_deriv_nonpos hx) pi_pos.le
  have he : (∫ x in Icc 0 Real.pi, (-(2*sqrt α)*sin x) •
      (mpDensity α (mpAngle α x)*g (mpAngle α x))) =
      -(∫ x in Icc 0 Real.pi, (2*α/Real.pi)*((sin x)^2/mpAngle α x)*g (mpAngle α x)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    simp only [smul_eq_mul]
    calc
      _ = -((2*sqrt α*sin x)*mpDensity α (mpAngle α x)*g (mpAngle α x)) := by ring
      _ = _ := by rw [mpAngle_density_jacobian hα.le hx]
  rw [he,(mpAngle_endpoints hα.le).1,(mpAngle_endpoints hα.le).2] at h
  exact (neg_injective h).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_MPDensityIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrability and exact mass of the literal MP density, including the critical aspect ratio. -/
noncomputable section
open Real Set MeasureTheory
namespace InvariantIsing

lemma mpDensity_nonneg {α x : ℝ} (hx : x ∈ Icc (marchenkoPasturA α) (marchenkoPasturB α)) :
    0 ≤ mpDensity α x := by
  have hA : 0 ≤ marchenkoPasturA α := sq_nonneg _
  have hx0 := hA.trans hx.1
  exact div_nonneg (sqrt_nonneg _) (by positivity)

lemma mpDensity_integrable {α : ℝ} (hα : 0 < α) :
    IntegrableOn (mpDensity α) (Icc (marchenkoPasturA α) (marchenkoPasturB α)) := by
  have hi : IntegrableOn (fun x => (2*α/Real.pi)*((sin x)^2/mpAngle α x)) (Icc 0 Real.pi) := by
    exact ((intervalIntegrable_iff_integrableOn_Icc_of_le pi_pos.le).mp
      (mp_angular_sine_integrable hα)).const_mul (2*α/Real.pi)
  have hc : IntegrableOn (fun x => (-(2*sqrt α)*sin x) • mpDensity α (mpAngle α x)) (Icc 0 Real.pi) := by
    apply hi.neg.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    simp only [Pi.neg_apply,smul_eq_mul]
    calc
      _ = -((2*sqrt α*sin x)*mpDensity α (mpAngle α x)) := by rw [mpAngle_density_jacobian hα.le hx]
      _ = _ := by ring
  have he := (integrableOn_Icc_deriv_smul_iff_of_deriv_nonpos
    (f := mpAngle α) (f' := fun x => -(2*sqrt α)*sin x) (g := mpDensity α)
    (continuous_mpAngle α).continuousOn (fun x _ => mpAngle_hasDerivAt α x)
    (fun _ hx => mpAngle_deriv_nonpos hx) pi_pos.le).mp hc
  simpa only [(mpAngle_endpoints hα.le).1,(mpAngle_endpoints hα.le).2] using he

theorem mpDensity_integral {α : ℝ} (hα : 0 < α) :
    (∫ x in Icc (marchenkoPasturA α) (marchenkoPasturB α), mpDensity α x) = min 1 α := by
  have h := mpDensity_substitution hα (fun _ => 1)
  simp only [mul_one] at h
  rw [h,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le pi_pos.le,
    intervalIntegral.integral_const_mul]
  exact mp_angular_continuous_mass hα

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_MPDensityProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization of the literal density and atom appearing in the MP application input. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace InvariantIsing

lemma marchenkoPasturMeasure_eq_density (α : ℝ) :
    marchenkoPasturMeasure α = ENNReal.ofReal (max (1-α) 0) • Measure.dirac 0+
      (volume.restrict (Icc (marchenkoPasturA α) (marchenkoPasturB α))).withDensity
        (fun x => ENNReal.ofReal (mpDensity α x)) := by
  unfold marchenkoPasturMeasure
  rw [withDensity_indicator measurableSet_Icc]
  rfl

theorem marchenkoPastur_probability {α : ℝ} (hα : 0 < α) :
    IsProbabilityMeasure (marchenkoPasturMeasure α) := by
  constructor
  rw [marchenkoPasturMeasure_eq_density,Measure.add_apply,Measure.smul_apply,
    measure_univ,smul_eq_mul,mul_one,withDensity_apply _ MeasurableSet.univ]
  simp only [setLIntegral_univ]
  have hn : 0 ≤ᵐ[volume.restrict (Icc (marchenkoPasturA α) (marchenkoPasturB α))] mpDensity α :=
    (ae_restrict_mem measurableSet_Icc).mono (fun _ hx => mpDensity_nonneg hx)
  rw [← ofReal_integral_eq_lintegral_ofReal (mpDensity_integrable hα) hn,
    mpDensity_integral hα,
    ← ENNReal.ofReal_add (le_max_right (1-α) 0) (le_min (by norm_num) hα.le),
    mp_total_mass,ENNReal.ofReal_one]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarCompactness
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

lemma isClosed_specialOrthogonal (N : ℕ) :
    IsClosed (Matrix.specialOrthogonalGroup (Fin N) ℝ : Set (Matrix (Fin N) (Fin N) ℝ)) := by
  have he : (Matrix.specialOrthogonalGroup (Fin N) ℝ : Set (Matrix (Fin N) (Fin N) ℝ)) =
      {A | A*A.transpose=1} ∩ {A | A.det=1} := by
    ext A
    simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,SetLike.mem_coe,
      Matrix.mem_specialOrthogonalGroup_iff,Matrix.mem_orthogonalGroup_iff]
  rw [he]
  apply IsClosed.inter
  · apply isClosed_eq <;> fun_prop
  · apply isClosed_eq <;> fun_prop

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarFrobeniusBracket
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact Frobenius bracket contraction for the special orthogonal algebra. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

/-- The real, unnormalized Frobenius bilinear form. -/
def matrixFrobeniusPair {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  (A.transpose * B).trace

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial differentiation along the actual special-orthogonal rotations. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators Matrix.Norms.Frobenius
namespace InvariantIsing

/-- Coordinate evaluation in the Frobenius matrix space. -/
def haarMatrixCoordinate {N : ℕ} (i j : Fin N) :
    Matrix (Fin N) (Fin N) ℝ →L[ℝ] ℝ :=
  (show Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] ℝ from
    { toFun := fun M => M i j
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }).toContinuousLinearMap

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_RotationMatrix
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

def rotationMatrix {N : ℕ} (R : Rotation N) : Matrix (Fin N) (Fin N) ℝ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin N) ℝ).toBasis R.toLinearMap

lemma rotationMatrix_apply {N : ℕ} (R : Rotation N) (i j : Fin N) :
    rotationMatrix R i j = R (EuclideanSpace.single j 1) i := by
  rw [rotationMatrix,LinearMap.toMatrix_apply]
  change (R (EuclideanSpace.basisFun (Fin N) ℝ j)) i = _
  rw [EuclideanSpace.basisFun_apply]

lemma rotationMatrix_mem {N : ℕ} (R : Rotation N) :
    rotationMatrix R ∈ Matrix.orthogonalGroup (Fin N) ℝ :=
  R.toMatrix_mem_unitaryGroup (EuclideanSpace.basisFun (Fin N) ℝ)
    (EuclideanSpace.basisFun (Fin N) ℝ)

@[simp] lemma rotationMatrix_one {N : ℕ} : rotationMatrix (1 : Rotation N) = 1 :=
  LinearMap.toMatrix_one _

def hyperplaneReflection {N : ℕ} (v : EuclideanSpace ℝ (Fin N)) : Rotation N :=
  (ℝ ∙ v)ᗮ.reflection

@[simp] lemma hyperplaneReflection_zero {N : ℕ} :
    hyperplaneReflection (0 : EuclideanSpace ℝ (Fin N)) = 1 := by
  apply LinearIsometryEquiv.ext
  intro x
  apply Submodule.reflection_mem_subspace_eq_self
  simp

lemma hyperplaneReflection_apply {N : ℕ} (v x : EuclideanSpace ℝ (Fin N)) :
    hyperplaneReflection v x = x-(2*(inner ℝ v x/‖v‖^2)) • v := by
  rw [hyperplaneReflection,Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply]
  module

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_PositiveExponentialSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Monotone positive truncations of the scalar exponential series. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace InvariantIsing

def positiveExpSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), x^k/(Nat.factorial k : ℝ)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_CompactSpectralClipping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Clipped spectral probability laws on their compact interval. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace InvariantIsing

def compactSpectralClip (R : ℝ) (hR : 0 ≤ R) (x : ℝ) : Icc (0 : ℝ) R :=
  ⟨spectralClip 0 R x,spectralClip_mem hR x⟩

lemma continuous_compactSpectralClip (R : ℝ) (hR : 0 ≤ R) : Continuous (compactSpectralClip R hR) :=
  (continuous_spectralClip 0 R).subtype_mk _

def compactClippedLaw (R : ℝ) (hR : 0 ≤ R) (μ : ProbabilityMeasure ℝ) :
    ProbabilityMeasure (Icc (0 : ℝ) R) := μ.map (f := (compactSpectralClip R hR)) (by first | (apply Continuous.aemeasurable; apply continuous_compactSpectralClip <;> assumption) | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end InvariantIsing

end

end OAI
end



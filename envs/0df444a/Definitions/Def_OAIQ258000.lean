-- Prove2me | Definitions.Def_OAIQ258000
-- name    : OAIQ258000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T05:11:44.120016+00:00
-- url     : https://prove2.me/theorems/87e253c4-7369-48a6-9e6f-722a19f06c6d
-- title:
--   Definitions bundle OAIQ258000 of the split of OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 266 declarations of OpenAI's Lean: 72 definitions, 8 inductive types or structures, 3 instances and 183 theorems. The definitions and types are `MeasureTheory.ProbabilityMeasure.mapAE`, `OAI.InvariantIsing.BilinearGaussianIndex`, `OAI.InvariantIsing.CascadeSeedRegular`, `OAI.InvariantIsing.CavityFactorBlocks`, `OAI.InvariantIsing.CavityLabeledDisorder`, `OAI.InvariantIsing.CavityLabeledState`, `OAI.InvariantIsing.CavityProjectorFrame`, `OAI.InvariantIsing.CavityProjectorTensorIndex`, `OAI.InvariantIsing.CavityReplicaNode`, `OAI.InvariantIsing.CavitySpinState`, `OAI.InvariantIsing.CompactOverlapTest`, `OAI.InvariantIsing.CompactSpectralPartition`, `OAI.InvariantIsing.CompactSpectralPartition.Positive`, `OAI.InvariantIsing.CompactSpectralPartition.cells`, `OAI.InvariantIsing.CompactSpectralPartition.edge`, `OAI.InvariantIsing.CompactSpectralPartition.law`, `OAI.InvariantIsing.CompactSpectralPartition.lowerValue`, `OAI.InvariantIsing.CompactSpectralPartition.upperValue`, `OAI.InvariantIsing.CompactSpectralPartition.value`, `OAI.InvariantIsing.CompactSpectralPartition.weight`, `OAI.InvariantIsing.DavidsonSzarekInput`, `OAI.InvariantIsing.FieldAffineStep`, `OAI.InvariantIsing.FieldCovariate`, `OAI.InvariantIsing.FieldFiniteFamily`, `OAI.InvariantIsing.FieldFiniteFamily.affineDifferential`, `OAI.InvariantIsing.FieldFiniteFamily.affineLaw`, `OAI.InvariantIsing.FieldFiniteFamily.affineMomentCap`, `OAI.InvariantIsing.FieldFiniteFamily.affineShift`, `OAI.InvariantIsing.FieldFiniteFamily.curvature`, `OAI.InvariantIsing.FieldFiniteFamily.mean`, `OAI.InvariantIsing.FieldFiniteFamily.mixedMean`, `OAI.InvariantIsing.FieldFiniteFamily.mixedMeanCap`, `OAI.InvariantIsing.FieldFiniteFamily.secondMean`, `OAI.InvariantIsing.FieldFiniteFamily.secondMeanCap`, `OAI.InvariantIsing.FieldFiniteFamily.shiftPoint`, `OAI.InvariantIsing.FieldFiniteFamily.shiftedHessian`, `OAI.InvariantIsing.FieldFiniteFamily.shiftedMean`, `OAI.InvariantIsing.FieldFiniteFamily.shiftedMixed`, `OAI.InvariantIsing.FieldFiniteFamily.shiftedTangent`, `OAI.InvariantIsing.FieldFiniteFamily.tangent` and 40 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `InvariantIsing_Arrays_NSpinTensorBackwardDerivative`, `InvariantIsing_Arrays_NSpinTensorCascade`, `InvariantIsing_Arrays_OverlapTestDiagonal`, `InvariantIsing_Arrays_PerturbationFeatures`, `InvariantIsing_Cavity_CavityContinuousCutoff`, `InvariantIsing_Cavity_CavityGaussianNodePrior`, `InvariantIsing_Cavity_CavityLabeledModel`, `InvariantIsing_Cavity_CavityLabeledProjectors`, `InvariantIsing_Cavity_CavityProjectorTensor`, `InvariantIsing_Cavity_CavityRootedSpinTransport`, `InvariantIsing_Core_Model`, `InvariantIsing_Fields_CascadeMarking`, `InvariantIsing_Fields_CascadeSeedRegular`, `InvariantIsing_Fields_CascadeSeedTree`, `InvariantIsing_Fields_Field`, `InvariantIsing_Fields_FieldAffineAverageDerivative`, `InvariantIsing_Fields_FieldAffineMoments`, `InvariantIsing_Fields_FieldAffineRecursion`, `InvariantIsing_Fields_FieldCommonRefinement`, `InvariantIsing_Fields_FieldFiniteAverageDerivative`, `InvariantIsing_Fields_FieldFiniteCoordinateAverage`, `InvariantIsing_Fields_FieldFiniteCoordinates`, `InvariantIsing_Fields_FieldFiniteCovariance`, `InvariantIsing_Fields_FieldFiniteFamily`, `InvariantIsing_Fields_FieldFiniteLocal`, `InvariantIsing_Fields_FieldFiniteMeasurable`, `InvariantIsing_Fields_FieldFiniteMoments`, `InvariantIsing_Fields_FieldFiniteRecursion`, `InvariantIsing_Fields_FieldFiniteShift`, `InvariantIsing_Fields_FieldFiniteShiftBounds`, `InvariantIsing_Fields_FieldFiniteShiftData`, `InvariantIsing_Fields_FieldFiniteTiltDerivative`, `InvariantIsing_Fields_FieldFiniteTransformBounds`, `InvariantIsing_Fields_FieldFiniteTransformData`, `InvariantIsing_Fields_FieldFiniteTransformDerivative`, `InvariantIsing_Fields_FieldGaussianFamilyEnvelope`, `InvariantIsing_Fields_FieldGaussianFamilyGenerator`, `InvariantIsing_Fields_FieldGaussianFamilyRaw`, `InvariantIsing_Fields_FieldGaussianIntegrability`, `InvariantIsing_Fields_FieldGaussianPairDerivative`, `InvariantIsing_Fields_FieldGaussianQuadraticEnvelope`, `InvariantIsing_Fields_FieldGaussianTiltMoments`, `InvariantIsing_Fields_FieldGaussianTransformLaw`, `InvariantIsing_Fields_FieldHeightChart`, `InvariantIsing_Fields_FieldMagnetization`, `InvariantIsing_Fields_FieldMajorantFold`, `InvariantIsing_Fields_FieldParameterGrowth`, `InvariantIsing_Fields_FieldRealVariance`, `InvariantIsing_Fields_FieldRefineCut`, `InvariantIsing_Fields_FieldSecondFamily`, `InvariantIsing_Fields_FieldSmoothFamily`, `InvariantIsing_Fields_FieldSpinDerivative`, `InvariantIsing_Fields_FieldSpinSecondDerivative`, `InvariantIsing_Fields_FieldSpinTransition`, `InvariantIsing_Fields_FieldTiltAverageDerivative`, `InvariantIsing_Fields_FieldTiltedPairDerivative`, `InvariantIsing_Gaussian_BilinearGaussianComparison`, `InvariantIsing_Gaussian_GaussianPatternModel`, `InvariantIsing_Gaussian_GaussianPatternPublishedInputs`, `InvariantIsing_Gaussian_GaussianPatternRotation`, `InvariantIsing_Haar_Rotation`, `InvariantIsing_Pressure_RandomSpectralBound`, `InvariantIsing_Spectral_CompactPartitionPressure`, `InvariantIsing_Spectral_CompactSpectralPartition`, `InvariantIsing_Spectral_PositiveSpectralLabels`, `InvariantIsing_Spectral_SpectralBallPartition`, `InvariantIsing_Spectral_SpectralPartitionIndex`, `InvariantIsing_Spectral_SpectralPartitionLaw`, `IsingPerceptron_BoundedTiltAverage`, `IsingPerceptron_GaussianIntegration`, `IsingPerceptron_MonomialGgAtMinimum`, `IsingPerceptron_VariationalDefs`.
--
--   **Imports.** It imports the published bundles `Def_InvariantIsing` and `Def_IsingFiniteness`; the bundle `OAIQ4Ip000` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ258003` and `OAIQ258004`; the statements `OAI.InvariantIsing.cavity_spectral_haar_test_tendsto`, `OAI.InvariantIsing.davidsonSzarek_proved`, `OAI.InvariantIsing.gaussianPattern_spectralExcess_tendsto`, `OAI.InvariantIsing.spectral_clip_mean_field_pressure_close` and `OAI.InvariantIsing.spectral_clip_mean_pressure_close`; the proofs of `OAI.InvariantIsing.cavity_cascade_spin_block_tendsto`, `OAI.InvariantIsing.cavity_quadratic_regular_ae`, `OAI.InvariantIsing.cavity_quadratic_root_tree_law`, `OAI.InvariantIsing.cavity_residual_innovation_leaf_law`, `OAI.InvariantIsing.cavity_residual_partition_log_integral`, `OAI.InvariantIsing.cavity_residual_partition_pos_finite` and `OAI.InvariantIsing.gaussianPattern_spectralExcess_tendsto`.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Sort
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
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
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_InvariantIsing
import Definitions.Def_IsingFiniteness
import Definitions.Def_OAIQ4Ip000

section
-- module Solutions.OAIQ258_II.Compat
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
open scoped Matrix in
/-- Mathlib d13f23b's `Matrix.posSemidef_is_closed` (real matrices): positive semidefinite matrices are
closed (EinsteinFour JacobiCompressionLimit, oaiq-091). -/
theorem _root_.Matrix.posSemidef_is_closed {n : Type*} [Fintype n] :
    IsClosed {M : Matrix n n ℝ | M.PosSemidef} := by
  have h : {M : Matrix n n ℝ | M.PosSemidef} =
      {M : Matrix n n ℝ | M.IsHermitian} ∩
        ⋂ x : n → ℝ, {M : Matrix n n ℝ | 0 ≤ star x ⬝ᵥ (M *ᵥ x)} := by
    ext M
    simp [Matrix.posSemidef_iff_dotProduct_mulVec]
  rw [h]
  refine IsClosed.inter ?_ (isClosed_iInter fun x => ?_)
  · exact isClosed_eq (Continuous.matrix_conjTranspose continuous_id) continuous_id
  · exact isClosed_le continuous_const (by fun_prop)
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
/-- Mathlib d13f23b's `MeasurableSpace (Matrix m n α)` (Mathlib/Analysis/Matrix/MeasurableSpace.lean): the product structure
(InvariantIsing, q251). Explicitly named: the platform's `Def_InvariantIsing` declares an anonymous copy of the same
instance. -/
instance _root_.Matrix.compatMeasurableSpace {m n α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Matrix m n α) :=
  inferInstanceAs <| MeasurableSpace (m → n → α)
/-- Mathlib d13f23b's `BorelSpace (Matrix m n α)` (Mathlib/Analysis/Matrix/MeasurableSpace.lean; InvariantIsing, q258). -/
instance _root_.Matrix.compatBorelSpace {m n α : Type*} [Countable m] [Countable n] [MeasurableSpace α]
    [TopologicalSpace α] [SecondCountableTopology α] [BorelSpace α] : BorelSpace (Matrix m n α) :=
  inferInstanceAs <| BorelSpace (m → n → α)
/-- d13f23b's `Measurable.of_eval_matrix` (q258). -/
lemma _root_.Measurable.of_eval_matrix {m n α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (M : β → Matrix m n α) (hM : ∀ i j, Measurable (M · i j)) : Measurable M :=
  measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j => hM i j))
/-- d13f23b's `CFC.measurable_sqrt` (Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Measurable.lean; q258). -/
lemma _root_.CFC.measurable_sqrt {A : Type*} [NonUnitalNormedRing A] [StarRing A] [NormedSpace ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [PartialOrder A] [StarOrderedRing A]
    [NonnegSpectrumClass ℝ A] [NonUnitalIsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    [CompleteSpace A] [ContinuousStar A] [OrderClosedTopology A] [MeasurableSpace A] [BorelSpace A] :
    Measurable (CFC.sqrt : A → A) := by
  have h_measurable : MeasurableSet {S : A | 0 ≤ S} :=
    (isClosed_le continuous_const continuous_id).measurableSet
  classical
  convert CFC.continuousOn_sqrt.measurable_piecewise (continuousOn_const (c := 0)) h_measurable
  ext S
  by_cases hS : 0 ≤ S
  · simp [hS]
  · simp [hS, CFC.sqrt_of_not_nonneg]
end OAICompat434
open scoped MatrixOrder in
/-- The Loewner order on real matrices is closed (d13f23b has `OrderClosedTopology` for it; InvariantIsing, q258): the set
`A ≤ B` is the preimage of the closed positive semidefinite cone. -/
instance _root_.Matrix.compatOrderClosedTopology {n : Type*} [Fintype n] [DecidableEq n] :
    OrderClosedTopology (Matrix n n ℝ) :=
  ⟨by
    have h : {p : Matrix n n ℝ × Matrix n n ℝ | p.1 ≤ p.2} =
        (fun p : Matrix n n ℝ × Matrix n n ℝ => p.2 - p.1) ⁻¹' {M | M.PosSemidef} := by
      ext p; exact Matrix.le_iff
    rw [h]
    exact Matrix.posSemidef_is_closed.preimage (continuous_snd.sub continuous_fst)⟩
open Matrix in
/-- d13f23b's `Matrix.continuous_uncurry_toEuclideanCLM`, for real matrices (q258). -/
theorem _root_.Matrix.continuous_uncurry_toEuclideanCLM_real {n : Type*} [Fintype n] [DecidableEq n] :
    Continuous (fun p : Matrix n n ℝ × EuclideanSpace ℝ n => toEuclideanCLM (n := n) (𝕜 := ℝ) p.1 p.2) := by
  have h : (fun p : Matrix n n ℝ × EuclideanSpace ℝ n => toEuclideanCLM (n := n) (𝕜 := ℝ) p.1 p.2) =
      fun p => WithLp.toLp 2 (p.1 *ᵥ p.2.ofLp) := by
    ext p i
    simp
  rw [h]
  refine (PiLp.continuous_toLp 2 _).comp ?_
  refine continuous_pi fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  fun_prop
open Matrix in
@[fun_prop]
theorem _root_.Matrix.measurable_uncurry_toEuclideanCLM_real {n : Type*} [Fintype n] [DecidableEq n] :
    Measurable (fun p : Matrix n n ℝ × EuclideanSpace ℝ n => toEuclideanCLM (n := n) (𝕜 := ℝ) p.1 p.2) :=
  Matrix.continuous_uncurry_toEuclideanCLM_real.measurable
open scoped MatrixOrder in
@[fun_prop]
theorem _root_.Matrix.measurable_cfc_sqrt_real {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Measurable (fun S : Matrix ι ι ℝ => CFC.sqrt S) := by
  open scoped Matrix.Norms.L2Operator in
  exact CFC.measurable_sqrt
open MeasureTheory in
/-- The push-forward of a probability measure by an arbitrary function: `ProbabilityMeasure.map` when it is a.e.
measurable, a Dirac measure otherwise. OpenAI's Mathlib has a total `ProbabilityMeasure.map`; ours needs the proof
(InvariantIsing `cavityBlockMarkedLaw`, q258). -/
noncomputable def _root_.MeasureTheory.ProbabilityMeasure.mapAE {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (ν : ProbabilityMeasure Ω) (f : Ω → Ω') : ProbabilityMeasure Ω' := by
  classical
  exact if h : AEMeasurable f (ν : Measure Ω) then ν.map h
    else ⟨Measure.dirac (f (Classical.choice (by
      by_contra hne
      rw [not_nonempty_iff] at hne
      have h1 := measure_univ (μ := (ν : Measure Ω))
      rw [Set.univ_eq_empty_iff.mpr hne] at h1
      simp at h1))), inferInstance⟩

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

@[simp] lemma gaussianOperator_zero_variance (a : ℝ) (f : ℝ → ℝ) :
    gaussianOperator a 0 f = f := by
  funext z
  by_cases ha : a = 0
  · simp [gaussianOperator, ha]
  · simp [gaussianOperator, ha]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_GaussianIntegration
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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

lemma hasDerivAt_standardGaussianPDF (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h := (((hasDerivAt_id x).pow 2).neg.div_const 2).exp.const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  · ext y
    simp [gaussianPDFReal]
  · norm_num [gaussianPDFReal]
    ring

lemma integrable_gaussian_iff {f : ℝ → ℝ} :
    Integrable f (gaussianReal 0 1) ↔
      Integrable (fun x => gaussianPDFReal 0 1 x * f x) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  rw [integrable_withDensity_iff_integrable_smul']
  · simp [gaussianPDF, ENNReal.toReal_ofReal, gaussianPDFReal_nonneg]
  · exact measurable_gaussianPDF _ _
  · exact ae_of_all _ (fun x => by simp [gaussianPDF])

lemma gaussian_integration_by_parts {f f' : ℝ → ℝ} (hd : ∀ x, HasDerivAt f (f' x) x)
    (hf : Integrable f (gaussianReal 0 1))
    (hf' : Integrable f' (gaussianReal 0 1))
    (hxf : Integrable (fun x => x * f x) (gaussianReal 0 1)) :
    (∫ x, x * f x ∂gaussianReal 0 1) = ∫ x, f' x ∂gaussianReal 0 1 := by
  have hh := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := f) (u' := f') (v := gaussianPDFReal 0 1)
    (v' := fun x => -x * gaussianPDFReal 0 1 x)
    (fun x _ => hd x) (fun x _ => hasDerivAt_standardGaussianPDF x)
  have h1 : Integrable (fun x => f x * (-x * gaussianPDFReal 0 1 x)) := by
    convert (integrable_gaussian_iff.mp hxf).neg using 1
    all_goals try with_reducible_and_instances rfl
    ext x; dsimp <;> ring
  have h2 : Integrable (fun x => f' x * gaussianPDFReal 0 1 x) := by
    simpa [mul_comm] using integrable_gaussian_iff.mp hf'
  have h3 : Integrable (fun x => f x * gaussianPDFReal 0 1 x) := by
    simpa [mul_comm] using integrable_gaussian_iff.mp hf
  specialize hh h1 h2 h3
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul] at *
  have heq : (fun x => f x * (-x * gaussianPDFReal 0 1 x)) =
      fun x => -(gaussianPDFReal 0 1 x * (x * f x)) := by ext x; ring
  rw [heq, integral_neg] at hh
  simpa [mul_comm] using neg_injective hh

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

variable {A : Type*} [MeasurableSpace A]

lemma integral_exp_pos (μ : Measure A) [IsProbabilityMeasure μ] (F : A → ℝ)
    {b : ℝ} (hi : Integrable (fun a => Real.exp (b*F a)) μ) :
    0 < ∫ a, Real.exp (b*F a) ∂μ := by
  apply (integral_pos_iff_support_of_nonneg (fun a => (Real.exp_pos _).le) hi).mpr
  simpa only [Function.support, ne_eq, Real.exp_ne_zero, not_false_eq_true, ofPred_true,
    measure_univ] using (zero_lt_one : (0 : ℝ≥0∞) < 1)

end IsingPerceptron

namespace IsingPerceptron
variable {S : Type*} [SeminormedAddCommGroup S] [MeasurableSpace S] [MeasurableAdd₂ S]

omit [MeasurableAdd₂ S] in
lemma integrable_exp_of_linearGrowth (μ : Measure S) (hμ : ExponentialNormMoments μ)
    {F : S → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F) (b : ℝ) :
    Integrable (fun s => Real.exp (b*F s)) μ := by
  obtain ⟨C,L,_,_,hbound⟩ := hG
  apply ((hμ (|b| *L)).const_mul (Real.exp (|b| *C))).mono'
    ((hF.const_mul b).exp).aestronglyMeasurable
  apply ae_of_all
  intro s
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  calc
    b*F s ≤ |b*F s| := le_abs_self _
    _ = |b| *|F s| := abs_mul _ _
    _ ≤ |b| *(C+L*‖s‖) := mul_le_mul_of_nonneg_left (hbound s) (abs_nonneg _)
    _ = |b| *C+(|b| *L)*‖s‖ := by ring

omit [MeasurableSpace S] [MeasurableAdd₂ S] in
lemma HasLinearGrowth.add_left {F : S → ℝ} (h : HasLinearGrowth F) (x : S) :
    HasLinearGrowth (fun a => F (x+a)) := by
  obtain ⟨C,L,hC,hL,h⟩ := h
  refine ⟨C+L*‖x‖, L, by positivity, hL, fun a => ?_⟩
  calc
    _ ≤ C+L*‖x+a‖ := h _
    _ ≤ C+L*(‖x‖+‖a‖) := add_le_add_right (mul_le_mul_of_nonneg_left (norm_add_le _ _) hL) C
    _ = C+L*‖x‖+L*‖a‖ := by ring

end IsingPerceptron

namespace IsingPerceptron
lemma gaussianReal_exponentialNormMoments (m : ℝ) (v : ℝ≥0) :
    ExponentialNormMoments (gaussianReal m v) := by
  intro a
  simpa only [Real.norm_eq_abs] using integrable_exp_mul_abs
    (integrable_exp_mul_gaussianReal (μ := m) (v := v) a)
    (integrable_exp_mul_gaussianReal (μ := m) (v := v) (-a))

end IsingPerceptron

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


lemma HasLinearGrowth.scale_argument {F : ℝ → ℝ} (h : HasLinearGrowth F) (a : ℝ) :
    HasLinearGrowth (fun x => F (a*x)) := by
  obtain ⟨C,L,hC,hL,h⟩ := h
  refine ⟨C,L*|a|,hC,mul_nonneg hL (abs_nonneg a),fun x => ?_⟩
  simpa only [Real.norm_eq_abs,abs_mul,mul_assoc] using h (a*x)

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
-- module Solutions.OAIQ258_II.IsingPerceptron_BoundedTiltAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded Tilt Average. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma integral_tilted_eq_div {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U A : Ω → ℝ) :
    (∫ x, A x ∂P.tilted U) = (∫ x, Real.exp (U x)*A x ∂P) / (∫ x, Real.exp (U x) ∂P) := by
  rw [integral_tilted]
  simp only [smul_eq_mul,div_mul_eq_mul_div,integral_div]

 

def gaussianTiltAverage (s d : ℝ) (U A : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ z, A (x+Real.sqrt s*z) ∂(gaussianReal 0 1).tilted (fun z => d*U (x+Real.sqrt s*z))

lemma gaussianTiltAverage_eq_div (s d : ℝ) (U A : ℝ → ℝ) (x : ℝ) :
    gaussianTiltAverage s d U A x =
      (∫ z, Real.exp (d*U (x+Real.sqrt s*z))*A (x+Real.sqrt s*z) ∂gaussianReal 0 1) /
        (∫ z, Real.exp (d*U (x+Real.sqrt s*z)) ∂gaussianReal 0 1) :=
  integral_tilted_eq_div _ _ _

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma bounded_generator {D DD : ℝ → ℝ} {C L : ℝ}
    (hC : ∀ y, |D y| ≤ C) (hL : ∀ y, |DD y| ≤ L) (d y : ℝ) :
    |DD y + d*(D y)^2| ≤ L + |d| * C^2 := by
  refine (abs_add_le _ _).trans (add_le_add (hL y) ?_)
  rw [abs_mul,abs_pow]
  exact mul_le_mul_of_nonneg_left (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans (hC y)) |>.mpr (hC y)) (abs_nonneg _)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma measurable_gaussianTransform_param {E : Type*} [MeasurableSpace E]
    {U : E → ℝ → ℝ} {s x : E → ℝ}
    (hU : Measurable (fun p : E × ℝ => U p.1 p.2)) (hs : Measurable s)
    (hx : Measurable x) (d : ℝ) :
    Measurable (fun t => gaussianTransform (s t) d (U t) (x t)) := by
  have hm : Measurable (fun p : E × ℝ => U p.1 (x p.1+Real.sqrt (s p.1)*p.2)) :=
    hU.comp (f := fun p : E × ℝ => (p.1,x p.1+Real.sqrt (s p.1)*p.2)) (by fun_prop)
  by_cases hz : d = 0
  · subst d
    simp only [gaussianTransform,ite_true, if_true]
    exact hm.stronglyMeasurable.integral_prod_right'.measurable
  · simp only [gaussianTransform,hz,ite_false, if_false]
    exact ((measurable_const.mul hm).exp.stronglyMeasurable.integral_prod_right'.measurable.log).div_const _

lemma measurable_gaussianTiltAverage_param {E : Type*} [MeasurableSpace E]
    {U A : E → ℝ → ℝ} {s x : E → ℝ}
    (hU : Measurable (fun p : E × ℝ => U p.1 p.2))
    (hA : Measurable (fun p : E × ℝ => A p.1 p.2)) (hs : Measurable s)
    (hx : Measurable x) (d : ℝ) :
    Measurable (fun t => gaussianTiltAverage (s t) d (U t) (A t) (x t)) := by
  have hm : Measurable (fun p : E × ℝ => U p.1 (x p.1+Real.sqrt (s p.1)*p.2)) :=
    hU.comp (f := fun p : E × ℝ => (p.1,x p.1+Real.sqrt (s p.1)*p.2)) (by fun_prop)
  have hn : Measurable (fun p : E × ℝ => A p.1 (x p.1+Real.sqrt (s p.1)*p.2)) :=
    hA.comp (f := fun p : E × ℝ => (p.1,x p.1+Real.sqrt (s p.1)*p.2)) (by fun_prop)
  simp only [gaussianTiltAverage_eq_div]
  exact ((measurable_const.mul hm).exp.mul hn).stronglyMeasurable.integral_prod_right'.measurable.div
    ((measurable_const.mul hm).exp.stronglyMeasurable.integral_prod_right'.measurable)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def pairLinear (a b : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] lemma pairLinear_apply (a b : ℝ) (p : ℝ × ℝ) :
    pairLinear a b p = a*p.1+b*p.2 := rfl

lemma norm_pairLinear_le (a b : ℝ) : ‖pairLinear a b‖ ≤ |a|+|b| := by
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ) (abs_nonneg _)).trans_eq (mul_one _)
  · rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ) (abs_nonneg _)).trans_eq (mul_one _)

lemma measurable_pairLinear {Ω : Type*} [MeasurableSpace Ω] {A B : Ω → ℝ}
    (hA : Measurable A) (hB : Measurable B) : Measurable (fun z => pairLinear (A z) (B z)) := by
  exact (hA.smul measurable_const).add (hB.smul measurable_const)

lemma integral_pairLinear {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {A B : Ω → ℝ} (hA : Integrable A P) (hB : Integrable B P) :
    (∫ z, pairLinear (A z) (B z) ∂P) = pairLinear (∫ z, A z ∂P) (∫ z, B z ∂P) := by
  simp only [pairLinear]
  rw [integral_add (hA.smul_const _) (hB.smul_const _),integral_smul_const,integral_smul_const]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma abs_div_two_sqrt_le {m s : ℝ} (hm : 0 < m) (hs : m ≤ s) (v : ℝ) :
    |v / (2*Real.sqrt s)| ≤ |v| / (2*Real.sqrt m) := by
  rw [abs_div,abs_of_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 (hm.trans_le hs)))]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hs) (by norm_num))

lemma affine_gaussian_shift_hasFDerivAt {U T X : ℝ × ℝ → ℝ} {I : Set ℝ}
    (hd : ∀ p, p.1 ∈ I → HasFDerivAt U (pairLinear (T p) (X p)) p)
    (a v z : ℝ) {p : ℝ × ℝ} (hp : p.1 ∈ I) (hs : 0 < a+v*p.1) :
    HasFDerivAt (fun q : ℝ × ℝ => U (q.1,q.2+Real.sqrt (a+v*q.1)*z))
      (pairLinear (T (p.1,p.2+Real.sqrt (a+v*p.1)*z) +
        X (p.1,p.2+Real.sqrt (a+v*p.1)*z)*(v/(2*Real.sqrt (a+v*p.1))*z))
        (X (p.1,p.2+Real.sqrt (a+v*p.1)*z))) p := by
  have hf : HasFDerivAt (fun q : ℝ × ℝ => q.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) p := hasFDerivAt_fst
  have hg : HasFDerivAt (fun q : ℝ × ℝ => q.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  have hr := ((hf.const_mul v).const_add a).sqrt hs.ne'
  have hh := (hd (p.1,p.2+Real.sqrt (a+v*p.1)*z) hp).comp p (hf.prodMk (hg.add (hr.mul_const z)))
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  all_goals
    apply ContinuousLinearMap.ext
    intro w
    simp [pairLinear]
    ring

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_CascadeMarking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The finite-depth Gaussian marking input used in the one-site functional.
The logarithmic terminal is unbounded; the linear-growth cascade theorem
supplies its integrability. This is the Gaussian specialization of
Bolthausen--Sznitman (1998), Appendix Proposition A.2.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

lemma integral_gaussianReal_zero_eq_standard (v : ℝ≥0) {F : ℝ → ℝ}
    (hF : Measurable F) :
    (∫ g, F g ∂gaussianReal 0 v) =
      ∫ g, F (Real.sqrt (v : ℝ) * g) ∂gaussianReal 0 1 := by
  have hm : (gaussianReal 0 1).map (fun g => Real.sqrt (v : ℝ) * g) =
      gaussianReal 0 v := by
    convert! gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt (v : ℝ)) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [mul_zero, mul_one]
    congr 1
    ext
    simp only [NNReal.coe_mk, Real.sq_sqrt v.coe_nonneg]
  rw [← hm]
  exact integral_map
    (show AEMeasurable (fun g : ℝ => Real.sqrt (v : ℝ) * g) (gaussianReal 0 1) from
      (measurable_id.const_mul _).aemeasurable) hF.aestronglyMeasurable

end InvariantIsing

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

@[simp] lemma abs_spinValue (b : Bool) : |spinValue b| = 1 := by
  cases b <;> norm_num [spinValue]

@[simp] lemma spinValue_sq (b : Bool) : spinValue b ^ 2 = 1 := by
  cases b <;> norm_num [spinValue]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_Rotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ising pressure on an orthogonal spectral orbit

The interaction is defined using a real linear isometry, so orthogonality
is part of its type. The bounds hold pointwise in the rotation; no Haar
or independence assumption is needed for these finite-volume estimates.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace InvariantIsing

@[simp] lemma spinVector_apply {N : ℕ} (σ : Spin N) (i : Fin N) :
    spinVector σ i = spinValue (σ i) := rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_PerturbationFeatures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite tensor features for spectral-overlap GG perturbations. -/

noncomputable section

open MeasureTheory
open scoped BigOperators Matrix

namespace InvariantIsing

abbrev SpectralTensorIndex {N m : ℕ} (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) :=
  (a : Fin m) → Fin (d a) → I a

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorCascade
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

abbrev SpinTensorIndex {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) :=
  Fin N ⊕ Sigma (fun j : Fin k => SpectralTensorIndex I (degree j))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorBackwardDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate derivatives through the actual finite Gaussian cascade recursion. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology NNReal ENNReal

namespace InvariantIsing

/-- The bounded coordinate derivative gives a local exponential dominator,
even when the terminal itself is unbounded. -/
lemma hasDerivAt_logMean_of_bounded_derivative
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (F D : ℝ → A → ℝ) (hF : ∀ s, Measurable (F s)) (hD : ∀ s, Measurable (D s))
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ s a, |D s a| ≤ K)
    (hd : ∀ s a, HasDerivAt (fun q => F q a) (D s a) s)
    {b : ℝ} (hb : b ≠ 0) (t : ℝ)
    (hi : Integrable (fun a => Real.exp (b * F t a)) μ) :
    HasDerivAt (fun s => logMean b μ (F s))
      (∫ a, D t a ∂μ.tilted (fun a => b * F t a)) t := by
  have hdiff (a : A) (s : ℝ) : |F s a - F t a| ≤ K * |s - t| := by
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun q (_ : q ∈ (Set.univ : Set ℝ)) => (hd q a).hasDerivWithinAt)
        (fun q _ => by simpa only [Real.norm_eq_abs] using hbound q a)
        convex_univ (Set.mem_univ t) (Set.mem_univ s)
  have hloc (s : ℝ) (hs : s ∈ Ioo (t - 1) (t + 1)) (a : A) :
      b * F s a ≤ b * F t a + |b| * K := by
    have hst : |s - t| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have h1 := (hdiff a s).trans (mul_le_of_le_one_right hK hst)
    have h2 : b * (F s a - F t a) ≤ |b| * K := (le_abs_self (b * (F s a - F t a))).trans
      (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg b))
    nlinarith
  let C := Real.exp (|b| * K) * (|b| * K)
  have hdom : Integrable (fun a => C * Real.exp (b * F t a)) μ := hi.const_mul C
  have hnorm (s : ℝ) (hs : s ∈ Ioo (t - 1) (t + 1)) (a : A) :
      ‖Real.exp (b * F s a) * (b * D s a)‖ ≤ C * Real.exp (b * F t a) := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_mul]
    calc
      _ ≤ Real.exp (b * F t a + |b| * K) * (|b| * K) :=
        mul_le_mul (Real.exp_le_exp.mpr (hloc s hs a))
          (mul_le_mul_of_nonneg_left (hbound s a) (abs_nonneg b))
          (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Real.exp_pos _).le
      _ = C * Real.exp (b * F t a) := by rw [Real.exp_add]; dsimp only [C] <;> ring
  obtain ⟨_, hI⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by linarith : t - 1 < t) (by linarith : t < t + 1))
    (Eventually.of_forall fun s => ((hF s).const_mul b).exp.aestronglyMeasurable) hi
    (((hF t).const_mul b).exp.mul ((hD t).const_mul b)).aestronglyMeasurable
    (ae_of_all _ fun a s hs => hnorm s hs a) hdom
    (ae_of_all _ fun a s _ => ((hd s a).const_mul b).exp)
  have hpos := IsingPerceptron.integral_exp_pos μ (F t) hi
  refine ((hI.log hpos.ne').div_const b).congr_deriv (Eq.symm ?_)
  · rw [integral_tilted_eq_div]
    have he : (∫ a, Real.exp (b * F t a) * (b * D t a) ∂μ) =
        b * ∫ a, Real.exp (b * F t a) * D t a ∂μ := by
      rw [← integral_const_mul]
      congr 1
      funext a
      ring
    rw [he]
    field_simp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldGaussianTransformLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact one-step Gaussian operator laws used to propagate the radial
comparison through the finite Ising field recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma field_gaussian_integral_shift (v : ℝ≥0) (z : ℝ) {F : ℝ → ℝ}
    (hF : Measurable F) :
    (∫ u, F u ∂gaussianReal z v) = ∫ u, F (z + u) ∂gaussianReal 0 v := by
  have hm : (gaussianReal 0 v).map (fun u => z + u) = gaussianReal z v := by
    simpa only [zero_add] using (gaussianReal_map_const_add (μ := 0) (v := v) z)
  rw [← hm]
  exact integral_map (show AEMeasurable (fun u : ℝ => z + u) (gaussianReal 0 v) from
    (measurable_const.add measurable_id).aemeasurable) hF.aestronglyMeasurable

lemma gaussianOperator_eq_gaussian_integral (v : ℝ≥0) {F : ℝ → ℝ}
    (hF : Measurable F) (z : ℝ) :
    gaussianOperator 0 v F z = ∫ u, F u ∂gaussianReal z v := by
  have hm : Measurable (fun u : ℝ => F (z + u)) :=
    hF.comp (measurable_const.add measurable_id)
  rw [field_gaussian_integral_shift v z hF,
    integral_gaussianReal_zero_eq_standard v (F := fun u => F (z + u)) hm]
  simp only [gaussianOperator, ite_true, if_true]

lemma gaussianOperator_eq_gaussian_exp_integral {ζ : ℝ} (hζ : ζ ≠ 0)
    (v : ℝ≥0) {F : ℝ → ℝ} (hF : Measurable F) (z : ℝ) :
    gaussianOperator ζ v F z =
      ζ⁻¹ * Real.log (∫ u, Real.exp (ζ * F u) ∂gaussianReal z v) := by
  have hm : Measurable (fun u : ℝ => Real.exp (ζ * F (z + u))) :=
    ((hF.comp (measurable_const.add measurable_id)).const_mul ζ).exp
  rw [field_gaussian_integral_shift v z (hF.const_mul ζ).exp,
    integral_gaussianReal_zero_eq_standard v (F := fun u => Real.exp (ζ * F (z + u))) hm]
  simp only [gaussianOperator, hζ, ite_false, if_false]

lemma field_gaussian_linear_integrable (v : ℝ≥0) (z : ℝ) {F : ℝ → ℝ}
    (hF : Measurable F) (hgrowth : HasLinearGrowth F) :
    Integrable F (gaussianReal z v) := by
  obtain ⟨C, L, _hC, hL, hbound⟩ := hgrowth
  have hi := (integrable_const C).add
    ((gaussianReal_exponentialNormMoments z v 1).const_mul L)
  apply hi.mono' hF.aestronglyMeasurable
  filter_upwards [] with u
  change |F u| ≤ C + L * Real.exp (1 * ‖u‖)
  rw [one_mul]
  exact (hbound u).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp ‖u‖)) hL))

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

lemma fieldIncrement_nonneg (h : FieldStep) (i : Fin (h.depth + 1)) :
    0 ≤ (fieldIncrement h i).2 := by
  unfold fieldIncrement
  split_ifs with hi
  · simpa using h.nonneg i
  · apply sub_nonneg.mpr
    apply h.ordered_height
    change i.val - 1 ≤ i.val
    omega

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

def fieldSpinTransition (ζ : ℝ) (v : ℝ≥0) (F a : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ u, a u ∂(gaussianReal z v).tilted (fun u => ζ * F u)

lemma fieldSpinTransition_eq_standard (ζ : ℝ) (v : ℝ≥0) {F a : ℝ → ℝ}
    (hF : Measurable F) (ha : Measurable a) (z : ℝ) :
    fieldSpinTransition ζ v F a z = gaussianTiltAverage v ζ F a z := by
  rw [fieldSpinTransition, integral_tilted_eq_div, gaussianTiltAverage_eq_div]
  have hnum : Measurable (fun u => Real.exp (ζ * F u) * a u) := (hF.const_mul ζ).exp.mul ha
  have hden : Measurable (fun u => Real.exp (ζ * F u)) := (hF.const_mul ζ).exp
  rw [field_gaussian_integral_shift v z hnum, field_gaussian_integral_shift v z hden]
  have hnums : Measurable (fun u => Real.exp (ζ * F (z + u)) * a (z + u)) :=
    hnum.comp (measurable_const.add measurable_id)
  have hdens : Measurable (fun u => Real.exp (ζ * F (z + u))) :=
    hden.comp (measurable_const.add measurable_id)
  rw [integral_gaussianReal_zero_eq_standard v
      (F := fun u => Real.exp (ζ * F (z + u)) * a (z + u)) hnums,
    integral_gaussianReal_zero_eq_standard v
      (F := fun u => Real.exp (ζ * F (z + u))) hdens]

lemma fieldSpinTransition_bound (ζ : ℝ) (v : ℝ≥0) {F a : ℝ → ℝ}
    (hF : Measurable F) (hgrowth : HasLinearGrowth F)
    {B : ℝ} (haB : ∀ u, |a u| ≤ B) (z : ℝ) :
    |fieldSpinTransition ζ v F a z| ≤ B := by
  have hw := integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hgrowth ζ
  have : IsProbabilityMeasure ((gaussianReal z v).tilted (fun u => ζ * F u)) :=
    MeasureTheory.isProbabilityMeasure_tilted hw
  have hb := norm_integral_le_of_norm_le_const (f := a) (C := B)
    (μ := (gaussianReal z v).tilted (fun u => ζ * F u))
    (Filter.Eventually.of_forall (fun u => by simpa only [Real.norm_eq_abs] using haB u))
  simpa only [fieldSpinTransition, Real.norm_eq_abs, measureReal_def, measure_univ,
    ENNReal.toReal_one, mul_one] using hb

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

/-- The non-root Gaussian increments in the given field step. -/
def scalarFieldIncrements (h : FieldStep) : List (ℝ × ℝ≥0) :=
  List.ofFn (fun i : Fin h.depth => ((fieldIncrement h i.succ).1,
    NNReal.mk (fieldIncrement h i.succ).2 (fieldIncrement_nonneg h i.succ)))

lemma scalarFieldIncrements_length (h : FieldStep) :
    (scalarFieldIncrements h).length = h.depth := by simp [scalarFieldIncrements]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianNodePrior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reindexing the actual shared Gaussian root, independent forest, and
replica-specific ordinary residuals as one independent node family. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

abbrev CavityReplicaNode (n r : ℕ) := Option (ForestVertex n) ⊕ Fin r

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRootedSpinTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Root-retaining transport of the full cavity spin probability. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

abbrev CavitySpinState (d k n : ℕ) :=
  (EuclideanSpace ℝ (Fin d) ×
    (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) × Spin k

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

abbrev CavityFactorBlocks (d n : ℕ) :=
  Matrix (Fin d) (Fin d) ℝ × (Matrix (Fin d) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ)

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

abbrev CavityLabeledDisorder (d n : ℕ) :=
  LabeledTree n × (EuclideanSpace ℝ (Fin d) × (ForestVertex n → EuclideanSpace ℝ (Fin d)))

abbrev CavityLabeledState (d k n : ℕ) :=
  (LabeledLeaf n × EuclideanSpace ℝ (Fin d)) × Spin k

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldGaussianIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted integrability needed for covariance differentiation of
the linearly growing scalar Ising recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma field_exp_mul_linear_integrable (v : ℝ≥0) (z ζ : ℝ) {F G : ℝ → ℝ}
    (hF : Measurable F) (hFg : HasLinearGrowth F)
    (hG : Measurable G) (hGg : HasLinearGrowth G) :
    Integrable (fun u => Real.exp (ζ * F u) * G u) (gaussianReal z v) := by
  obtain ⟨CF, LF, _hCF, _hLF, hFb⟩ := hFg
  obtain ⟨CG, LG, hCG, hLG, hGb⟩ := hGg
  have hi := ((gaussianReal_exponentialNormMoments z v) (|ζ| * LF + 1)).const_mul
    ((CG + LG) * Real.exp (|ζ| * CF))
  apply hi.mono' ((hF.const_mul ζ).exp.mul hG).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro u
  have he1 : 1 ≤ Real.exp ‖u‖ := Real.one_le_exp (norm_nonneg u)
  have hen : ‖u‖ ≤ Real.exp ‖u‖ := by linarith [Real.add_one_le_exp ‖u‖]
  have hGbound : |G u| ≤ (CG + LG) * Real.exp ‖u‖ := calc
    _ ≤ CG + LG * ‖u‖ := hGb u
    _ ≤ CG * Real.exp ‖u‖ + LG * Real.exp ‖u‖ :=
      add_le_add (by simpa only [mul_one] using mul_le_mul_of_nonneg_left he1 hCG)
        (mul_le_mul_of_nonneg_left hen hLG)
    _ = _ := by ring
  have hFbound : ζ * F u ≤ |ζ| * (CF + LF * ‖u‖) :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb u) (abs_nonneg ζ))
  change ‖Real.exp (ζ * F u) * G u‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (|ζ| * (CF + LF * ‖u‖)) * ((CG + LG) * Real.exp ‖u‖) :=
      mul_le_mul (Real.exp_le_exp.mpr hFbound) hGbound (abs_nonneg _) (Real.exp_pos _).le
    _ = ((CG + LG) * Real.exp (|ζ| * CF)) * Real.exp ((|ζ| * LF + 1) * ‖u‖) := by
      rw [show |ζ| * (CF + LF * ‖u‖) = |ζ| * CF + (|ζ| * LF) * ‖u‖ by ring,
        Real.exp_add, show (|ζ| * LF + 1) * ‖u‖ = (|ζ| * LF) * ‖u‖ + ‖u‖ by ring,
        Real.exp_add]
      ring

lemma field_gaussian_tilted_ibp {F D DD : ℝ → ℝ}
    (hF : Measurable F) (hFg : HasLinearGrowth F)
    (hD : Measurable D) (hDD : Measurable DD)
    {K C : ℝ} (hDb : ∀ u, |D u| ≤ K) (hDDb : ∀ u, |DD u| ≤ C)
    (hd : ∀ u, HasDerivAt F (D u) u) (hdd : ∀ u, HasDerivAt D (DD u) u)
    (r ζ z : ℝ) :
    (∫ u, u * D (z + r * u)
      ∂(gaussianReal 0 1).tilted (fun u => ζ * F (z + r * u))) =
      r * (∫ u, DD (z + r * u) + ζ * (D (z + r * u)) ^ 2
        ∂(gaussianReal 0 1).tilted (fun u => ζ * F (z + r * u))) := by
  let U := fun u => F (z + r * u)
  let A := fun u => Real.exp (ζ * U u) * D (z + r * u)
  let DA := fun u => r * (Real.exp (ζ * U u) *
    (DD (z + r * u) + ζ * (D (z + r * u)) ^ 2))
  have hUm : Measurable U := hF.comp (measurable_const.add (measurable_id.const_mul r))
  have hUg : HasLinearGrowth U := (hFg.add_left z).scale_argument r
  have hw := integrable_exp_of_linearGrowth (gaussianReal 0 1)
    (gaussianReal_exponentialNormMoments 0 1) hUm hUg ζ
  have hA : Integrable A (gaussianReal 0 1) := by
    exact hw.mul_bdd (hD.comp (measurable_const.add (measurable_id.const_mul r))).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun u => by simpa only [Real.norm_eq_abs] using hDb (z + r * u)))
  have hDA : Integrable DA (gaussianReal 0 1) := by
    apply Integrable.const_mul
    exact hw.mul_bdd
      ((hDD.comp (measurable_const.add (measurable_id.const_mul r))).add
        (((hD.comp (measurable_const.add (measurable_id.const_mul r))).pow_const 2).const_mul ζ)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun u => by
        simpa only [Real.norm_eq_abs] using bounded_generator hDb hDDb ζ (z + r * u)))
  have hAD (u : ℝ) : HasDerivAt A (DA u) u := by
    have harg : HasDerivAt (fun y => z + r * y) r u := by
      convert ((hasDerivAt_id u).const_mul r).const_add z using 1 <;>
        first | rfl | simp only [mul_one]
    have h1 : HasDerivAt (fun y => F (z + r * y)) (D (z + r * u) * r) u :=
      (hd (z + r * u)).comp u harg
    have h2 : HasDerivAt (fun y => D (z + r * y)) (DD (z + r * u) * r) u :=
      (hdd (z + r * u)).comp u harg
    convert ((h1.const_mul ζ).exp).mul h2 using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [A, DA, U]
    ring
  have hGm : Measurable (fun u => u * D (z + r * u)) :=
    measurable_id.mul (hD.comp (measurable_const.add (measurable_id.const_mul r)))
  have hGg : HasLinearGrowth (fun u => u * D (z + r * u)) := by
    refine ⟨0, |K|, le_rfl, abs_nonneg K, fun u => ?_⟩
    rw [abs_mul, Real.norm_eq_abs, zero_add]
    calc
      |u| * |D (z + r * u)| ≤ |u| * |K| :=
        mul_le_mul_of_nonneg_left ((hDb _).trans (le_abs_self K)) (abs_nonneg u)
      _ = _ := mul_comm _ _
  have hXA : Integrable (fun u => u * A u) (gaussianReal 0 1) := by
    convert field_exp_mul_linear_integrable 1 0 ζ hUm hUg hGm hGg using 1
    all_goals try with_reducible_and_instances rfl
    funext u
    dsimp only [A]
    ring
  have hibp := gaussian_integration_by_parts hAD hA hDA hXA
  simp only [integral_tilted_eq_div]
  have hnum : (∫ u, Real.exp (ζ * F (z + r * u)) * (u * D (z + r * u)) ∂gaussianReal 0 1) =
      r * ∫ u, Real.exp (ζ * F (z + r * u)) *
        (DD (z + r * u) + ζ * (D (z + r * u)) ^ 2) ∂gaussianReal 0 1 := by
    rw [← integral_const_mul]
    convert hibp using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext u
    dsimp only [A, DA, U]
    ring
  rw [hnum]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldGaussianQuadraticEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A Gaussian exponential envelope for the quadratic affine-noise terms
appearing in second covariance derivatives. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma field_one_add_abs_sq_le_exp (u : ℝ) :
    (1 + |u|) ^ 2 ≤ Real.exp (2 * |u|) := by
  have h : 1 + |u| ≤ Real.exp |u| := by linarith [Real.add_one_le_exp |u|]
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |u|) h 2
  calc
    (1 + |u|) ^ 2 ≤ (Real.exp |u|) ^ 2 := hs
    _ = Real.exp (2 * |u|) := by rw [two_mul, Real.exp_add]; ring

lemma field_gaussian_quadratic_envelope_integrable (C L : ℝ) :
    Integrable (fun u : ℝ => Real.exp (C + L * |u|) * (1 + |u|) ^ 2)
      (gaussianReal 0 1) := by
  have hi := ((gaussianReal_exponentialNormMoments 0 1) (L + 2)).const_mul (Real.exp C)
  apply hi.mono' (by fun_prop)
  apply Filter.Eventually.of_forall
  intro u
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  change Real.exp (C + L * |u|) * (1 + |u|) ^ 2 ≤
    Real.exp C * Real.exp ((L + 2) * |u|)
  calc
    _ ≤ Real.exp (C + L * |u|) * Real.exp (2 * |u|) :=
      mul_le_mul_of_nonneg_left (field_one_add_abs_sq_le_exp u) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSpinDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial differentiation of the scalar Gaussian operator. The payoff
may grow linearly; only its derivative is bounded. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma fieldSpinTransition_eq_shifted (ζ : ℝ) (v : ℝ≥0) {F a : ℝ → ℝ}
    (hF : Measurable F) (ha : Measurable a) (z : ℝ) :
    fieldSpinTransition ζ v F a z =
      ∫ u, a (z + u) ∂(gaussianReal 0 v).tilted (fun u => ζ * F (z + u)) := by
  rw [fieldSpinTransition, integral_tilted_eq_div, integral_tilted_eq_div]
  have hm : Measurable (fun u => Real.exp (ζ * F u) * a u) :=
    (hF.const_mul ζ).exp.mul ha
  rw [field_gaussian_integral_shift v z hm,
    field_gaussian_integral_shift v z (hF.const_mul ζ).exp]

lemma gaussianOperator_eq_logMean_shift {ζ : ℝ} (hζ : ζ ≠ 0)
    (v : ℝ≥0) {F : ℝ → ℝ} (hF : Measurable F) (z : ℝ) :
    gaussianOperator ζ v F z =
      logMean ζ (gaussianReal 0 v) (fun u => F (z + u)) := by
  rw [gaussianOperator_eq_gaussian_exp_integral hζ v hF,
    field_gaussian_integral_shift v z (hF.const_mul ζ).exp, logMean]
  ring

lemma hasDerivAt_gaussianOperator (ζ : ℝ) (v : ℝ≥0) {F D : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (hD : Measurable D)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ u, |D u| ≤ K)
    (hd : ∀ u, HasDerivAt F (D u) u) (z : ℝ) :
    HasDerivAt (gaussianOperator ζ v F) (fieldSpinTransition ζ v F D z) z := by
  have hshift (s u : ℝ) :
      HasDerivAt (fun q => F (q + u)) (D (s + u)) s := by
    convert (hd (s + u)).comp s ((hasDerivAt_id s).add_const u) using 1 <;>
      first | rfl | simp only [mul_one]
  have hm (s : ℝ) : Measurable (fun u => F (s + u)) :=
    hF.comp (measurable_const.add measurable_id)
  have hDm (s : ℝ) : Measurable (fun u => D (s + u)) :=
    hD.comp (measurable_const.add measurable_id)
  by_cases hζ : ζ = 0
  · subst ζ
    have hi := field_gaussian_linear_integrable v 0 (hm z) (hG.add_left z)
    obtain ⟨_, hI⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (Ioo_mem_nhds (by linarith : z - 1 < z) (by linarith : z < z + 1))
      (Eventually.of_forall fun s => (hm s).aestronglyMeasurable) hi
      (hDm z).aestronglyMeasurable
      (ae_of_all _ fun u s _ => by simpa only [Real.norm_eq_abs] using hbound (s + u))
      (integrable_const K) (ae_of_all _ fun u s _ => hshift s u)
    have he : gaussianOperator 0 v F = fun s => ∫ u, F (s + u) ∂gaussianReal 0 v := by
      funext s
      rw [gaussianOperator_eq_gaussian_integral v hF,
        field_gaussian_integral_shift v s hF]
    rw [he, fieldSpinTransition_eq_shifted 0 v hF hD]
    simpa only [zero_mul, tilted_const] using hI
  · have hi := integrable_exp_of_linearGrowth (gaussianReal 0 v)
      (gaussianReal_exponentialNormMoments 0 v) (hm z) (hG.add_left z) ζ
    have h := hasDerivAt_logMean_of_bounded_derivative (gaussianReal 0 v)
      (fun s u => F (s + u)) (fun s u => D (s + u)) hm hDm hK
      (fun s u => hbound (s + u)) hshift hζ z hi
    have he : gaussianOperator ζ v F =
        fun s => logMean ζ (gaussianReal 0 v) (fun u => F (s + u)) := by
      funext s
      exact gaussianOperator_eq_logMean_shift hζ v hF s
    rw [he, fieldSpinTransition_eq_shifted ζ v hF hD]
    exact h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldGaussianFamilyEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A local exponential envelope for the two-parameter scalar Gaussian
recursion. This is used with parameter and spatial coordinate together. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology NNReal

namespace InvariantIsing

lemma field_average_hasFDerivAt_of_envelope
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (U : (ℝ × ℝ) → ℝ → ℝ) (D : (ℝ × ℝ) → ℝ → (ℝ × ℝ) →L[ℝ] ℝ)
    {p : ℝ × ℝ} {S : Set (ℝ × ℝ)} (hS : S ∈ 𝓝 p)
    (hU : ∀ q, Measurable (U q)) (hD : AEStronglyMeasurable (D p) μ)
    (hi : Integrable (U p) μ) (ζ : ℝ)
    (hExp : Integrable (fun u => Real.exp (ζ * U p u)) μ)
    (B E : ℝ → ℝ) (hBi : Integrable B μ)
    (hEBi : Integrable (fun u => E u * B u) μ)
    (hB : ∀ q ∈ S, ∀ u, ‖D q u‖ ≤ B u)
    (hE : ∀ q ∈ S, ∀ u, Real.exp (ζ * U q u) ≤ E u)
    (hd : ∀ q ∈ S, ∀ u, HasFDerivAt (fun s => U s u) (D q u) q) :
    HasFDerivAt (fun q => if ζ = 0 then ∫ u, U q u ∂μ
        else Real.log (∫ u, Real.exp (ζ * U q u) ∂μ) / ζ)
      (∫ u, D p u ∂μ.tilted (fun u => ζ * U p u)) p := by
  by_cases hζ : ζ = 0
  · subst ζ
    simp only [ite_true, if_true, zero_mul, tilted_const]
    exact hasFDerivAt_integral_of_dominated_of_fderiv_le hS
      (Eventually.of_forall fun q => (hU q).aestronglyMeasurable) hi hD
      (ae_of_all _ fun u q hq => hB q hq u) hBi
      (ae_of_all _ fun u q hq => hd q hq u)
  · have hexp := hasFDerivAt_integral_of_dominated_of_fderiv_le hS
      (F := fun q u => Real.exp (ζ * U q u))
      (F' := fun q u => Real.exp (ζ * U q u) • (ζ • D q u))
      (Eventually.of_forall fun q => ((hU q).const_mul ζ).exp.aestronglyMeasurable)
      hExp (((hU p).const_mul ζ).exp.aestronglyMeasurable.smul (hD.const_smul ζ))
      (bound := fun u => |ζ| * (E u * B u))
      (ae_of_all _ fun u q hq => by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          norm_smul, Real.norm_eq_abs]
        calc
          _ = |ζ| * (Real.exp (ζ * U q u) * ‖D q u‖) := by ring
          _ ≤ |ζ| * (E u * B u) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul (hE q hq u) (hB q hq u) (norm_nonneg _)
                ((Real.exp_pos _).le.trans (hE q hq u))) (abs_nonneg ζ))
      (hEBi.const_mul |ζ|)
      (ae_of_all _ fun u q hq => ((hd q hq u).const_mul ζ).exp)
    have hp := IsingPerceptron.integral_exp_pos μ (U p) hExp
    have hraw : (∫ u, D p u ∂μ.tilted (fun u => ζ * U p u)) =
        (∫ u, Real.exp (ζ * U p u) ∂μ)⁻¹ •
          (∫ u, Real.exp (ζ * U p u) • D p u ∂μ) := by
      rw [integral_tilted, ← integral_smul]
      congr 1
      funext u
      rw [smul_smul]
      congr 1
      ring
    have hfactor : (∫ u, Real.exp (ζ * U p u) • (ζ • D p u) ∂μ) =
        ζ • (∫ u, Real.exp (ζ * U p u) • D p u ∂μ) := by
      rw [← integral_smul]
      congr 1
      funext u
      rw [smul_smul, smul_smul]
      congr 1
      ring
    convert (config := {transparency := .instances, preTransparency := .instances}) (hexp.log hp.ne').const_mul ζ⁻¹ using 1
    · funext q
      simp only [hζ, ite_false, if_false]
      ring
    · rw [hraw, hfactor]
      simp only [smul_smul]
      congr 1
      field_simp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldTiltAverageDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiation of the scalar tilted spin average. The potential
needs an exponential moment at the base point, rather than a global bound. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma parameter_exp_bound (U DU : ℝ → ℝ → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hDU : ∀ s u, |DU s u| ≤ C)
    (hd : ∀ s u, HasDerivAt (fun q => U q u) (DU s u) s)
    (ζ x s u : ℝ) (hs : s ∈ Ioo (x - 1) (x + 1)) :
    Real.exp (ζ * U s u) ≤ Real.exp (|ζ| * C) * Real.exp (ζ * U x u) := by
  have hdiff : |U s u - U x u| ≤ C * |s - x| := by
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun q (_ : q ∈ (univ : Set ℝ)) => (hd q u).hasDerivWithinAt)
        (fun q _ => by simpa only [Real.norm_eq_abs] using hDU q u)
        convex_univ (mem_univ x) (mem_univ s)
  have hdist : |s - x| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have h1 := hdiff.trans (mul_le_of_le_one_right hC hdist)
  have h2 : ζ * (U s u - U x u) ≤ |ζ| * C :=
    (le_abs_self _).trans (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left h1 (abs_nonneg ζ))
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith)

theorem hasDerivAt_tiltAverage_of_bounded_derivatives
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (U A DU DA : ℝ → ℝ → ℝ)
    (hU : ∀ s, Measurable (U s)) (hA : ∀ s, Measurable (A s))
    (hDU : ∀ s, Measurable (DU s)) (hDA : ∀ s, Measurable (DA s))
    {C M L : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hbDU : ∀ s u, |DU s u| ≤ C) (hbA : ∀ s u, |A s u| ≤ M)
    (hbDA : ∀ s u, |DA s u| ≤ L)
    (dU : ∀ s u, HasDerivAt (fun q => U q u) (DU s u) s)
    (dA : ∀ s u, HasDerivAt (fun q => A q u) (DA s u) s)
    (ζ x : ℝ) (hi : Integrable (fun u => Real.exp (ζ * U x u)) μ) :
    HasDerivAt (fun s => ∫ u, A s u ∂μ.tilted (fun u => ζ * U s u))
      ((∫ u, DA x u ∂μ.tilted (fun u => ζ * U x u)) +
        ζ * ((∫ u, A x u * DU x u ∂μ.tilted (fun u => ζ * U x u)) -
          (∫ u, A x u ∂μ.tilted (fun u => ζ * U x u)) *
            (∫ u, DU x u ∂μ.tilted (fun u => ζ * U x u)))) x := by
  have hS : Ioo (x - 1) (x + 1) ∈ 𝓝 x :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hE (s u : ℝ) (hs : s ∈ Ioo (x - 1) (x + 1)) :=
    parameter_exp_bound U DU hC hbDU dU ζ x s u hs
  have hAD (s u : ℝ) : |A s u * DU s u| ≤ M * C := by
    rw [abs_mul]
    exact mul_le_mul (hbA s u) (hbDU s u) (abs_nonneg _) hM
  have hprod {G : ℝ → ℝ} (hm : Measurable G) {K : ℝ} (hb : ∀ u, |G u| ≤ K) :
      Integrable (fun u => Real.exp (ζ * U x u) * G u) μ :=
    hi.mul_bdd hm.aestronglyMeasurable
      (ae_of_all _ fun u => by simpa only [Real.norm_eq_abs] using hb u)
  have hiA := hprod (hA x) (hbA x)
  have hiDA := hprod (hDA x) (hbDA x)
  have hiAD := hprod ((hA x).mul (hDU x)) (hAD x)
  change Integrable (fun u => Real.exp (ζ * U x u) * (A x u * DU x u)) μ at hiAD
  have hdDen (s u : ℝ) := ((dU s u).const_mul ζ).exp
  have hdNum (s u : ℝ) :
      HasDerivAt (fun q => Real.exp (ζ * U q u) * A q u)
        (Real.exp (ζ * U s u) * DA s u +
          ζ * (Real.exp (ζ * U s u) * (A s u * DU s u))) s := by
    convert (hdDen s u).mul (dA s u) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  obtain ⟨_, hden⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hS
    (Eventually.of_forall fun s => ((hU s).const_mul ζ).exp.aestronglyMeasurable) hi
    (((hU x).const_mul ζ).exp.mul ((hDU x).const_mul ζ)).aestronglyMeasurable
    (ae_of_all _ fun u s hs => by
      change |Real.exp (ζ * U s u) * (ζ * DU s u)| ≤ _
      rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_mul]
      calc
        _ ≤ (Real.exp (|ζ| * C) * Real.exp (ζ * U x u)) * (|ζ| * C) :=
          mul_le_mul (hE s u hs) (mul_le_mul_of_nonneg_left (hbDU s u) (abs_nonneg ζ))
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by positivity)
        _ = (Real.exp (|ζ| * C) * (|ζ| * C)) * Real.exp (ζ * U x u) := by ring)
    (hi.const_mul (Real.exp (|ζ| * C) * (|ζ| * C)))
    (ae_of_all _ fun u s _ => hdDen s u)
  obtain ⟨_, hnum⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hS
    (Eventually.of_forall fun s => (((hU s).const_mul ζ).exp.mul (hA s)).aestronglyMeasurable)
    hiA ((((hU x).const_mul ζ).exp.mul (hDA x)).add
      ((((hU x).const_mul ζ).exp.mul ((hA x).mul (hDU x))).const_mul ζ)).aestronglyMeasurable
    (ae_of_all _ fun u s hs => by
      change |Real.exp (ζ * U s u) * DA s u +
        ζ * (Real.exp (ζ * U s u) * (A s u * DU s u))| ≤ _
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_mul, abs_mul,
        abs_of_pos (Real.exp_pos _)]
      calc
        _ ≤ (Real.exp (|ζ| * C) * Real.exp (ζ * U x u)) * L +
            |ζ| * ((Real.exp (|ζ| * C) * Real.exp (ζ * U x u)) * (M * C)) :=
          add_le_add (mul_le_mul (hE s u hs) (hbDA s u) (abs_nonneg _) (by positivity))
            (mul_le_mul_of_nonneg_left
              (mul_le_mul (hE s u hs) (hAD s u) (abs_nonneg _) (by positivity)) (abs_nonneg ζ))
        _ = (Real.exp (|ζ| * C) * (L + |ζ| * (M * C))) *
            Real.exp (ζ * U x u) := by ring)
    (hi.const_mul (Real.exp (|ζ| * C) * (L + |ζ| * (M * C))))
    (ae_of_all _ fun u s _ => hdNum s u)
  have hp := IsingPerceptron.integral_exp_pos μ (U x) hi
  simp only [Pi.mul_apply] at hnum
  have hde : (∫ u, Real.exp (ζ * U x u) * (ζ * DU x u) ∂μ) =
      ζ * ∫ u, Real.exp (ζ * U x u) * DU x u ∂μ := by
    rw [← integral_const_mul]
    congr 1
    funext u
    ring
  have hne : (∫ u, Real.exp (ζ * U x u) * DA x u +
      ζ * (Real.exp (ζ * U x u) * (A x u * DU x u)) ∂μ) =
      (∫ u, Real.exp (ζ * U x u) * DA x u ∂μ) +
        ζ * ∫ u, Real.exp (ζ * U x u) * (A x u * DU x u) ∂μ := by
    rw [integral_add hiDA (hiAD.const_mul ζ), integral_const_mul]
  refine ((hnum.div hden hp.ne').congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv (Eq.symm ?_)
  · beta_reduce
    exact integral_tilted_eq_div _ _ _
  · simp only [integral_tilted_eq_div]
    rw [hde, hne]
    field_simp
    ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSpinSecondDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The derivative of the actual scalar spin transition, with a
linearly growing potential. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

theorem hasDerivAt_fieldSpinTransition (ζ : ℝ) (v : ℝ≥0)
    {F D a b : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hD : Measurable D) (ha : Measurable a) (hb : Measurable b)
    {C M L : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hDb : ∀ u, |D u| ≤ C) (hab : ∀ u, |a u| ≤ M) (hbb : ∀ u, |b u| ≤ L)
    (hd : ∀ u, HasDerivAt F (D u) u) (had : ∀ u, HasDerivAt a (b u) u)
    (z : ℝ) :
    HasDerivAt (fieldSpinTransition ζ v F a)
      (fieldSpinTransition ζ v F b z + ζ *
        (fieldSpinTransition ζ v F (fun u => a u * D u) z -
          fieldSpinTransition ζ v F a z * fieldSpinTransition ζ v F D z)) z := by
  have hi := integrable_exp_of_linearGrowth (gaussianReal 0 v)
    (gaussianReal_exponentialNormMoments 0 v)
    (hF.comp (measurable_const.add measurable_id)) (hG.add_left z) ζ
  have hd' (s u : ℝ) : HasDerivAt (fun q => F (q + u)) (D (s + u)) s := by
    convert (hd (s + u)).comp s ((hasDerivAt_id s).add_const u) using 1 <;>
      first | rfl | simp only [mul_one]
  have ha' (s u : ℝ) : HasDerivAt (fun q => a (q + u)) (b (s + u)) s := by
    convert (had (s + u)).comp s ((hasDerivAt_id s).add_const u) using 1 <;>
      first | rfl | simp only [mul_one]
  have h := hasDerivAt_tiltAverage_of_bounded_derivatives (gaussianReal 0 v)
    (fun s u => F (s + u)) (fun s u => a (s + u))
    (fun s u => D (s + u)) (fun s u => b (s + u))
    (fun s => hF.comp (measurable_const.add measurable_id))
    (fun s => ha.comp (measurable_const.add measurable_id))
    (fun s => hD.comp (measurable_const.add measurable_id))
    (fun s => hb.comp (measurable_const.add measurable_id))
    hC hM (fun s u => hDb (s + u)) (fun s u => hab (s + u))
    (fun s u => hbb (s + u)) hd' ha' ζ z hi
  have he : fieldSpinTransition ζ v F a =
      fun s => ∫ u, a (s + u) ∂(gaussianReal 0 v).tilted (fun u => ζ * F (s + u)) := by
    funext s
    exact fieldSpinTransition_eq_shifted ζ v hF ha s
  have hADm : Measurable (fun u => a u * D u) := ha.mul hD
  rw [he, fieldSpinTransition_eq_shifted ζ v hF hb,
    fieldSpinTransition_eq_shifted ζ v hF hADm,
    fieldSpinTransition_eq_shifted ζ v hF hD]
  exact h

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

lemma field_spatial_linearGrowth {F D : ℝ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hD : ∀ y, |D y| ≤ K)
    (hd : ∀ y, HasDerivAt F (D y) y) : HasLinearGrowth F := by
  refine ⟨|F 0|, K, abs_nonneg _, hK, fun y => ?_⟩
  have hdiff : |F y - F 0| ≤ K * |y| := by
    simpa only [Real.norm_eq_abs, sub_zero] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun z (_ : z ∈ (univ : Set ℝ)) => (hd z).hasDerivWithinAt)
        (fun z _ => by simpa only [Real.norm_eq_abs] using hD z)
        convex_univ (mem_univ 0) (mem_univ y)
  rw [Real.norm_eq_abs]
  calc
    |F y| = |F y - F 0 + F 0| := by congr 1; ring
    _ ≤ |F y - F 0| + |F 0| := abs_add_le _ _
    _ ≤ K * |y| + |F 0| := add_le_add_left hdiff _
    _ = _ := by ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldGaussianTiltMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform second-moment envelope for scalar Gaussian tilts whose
centered potential is Lipschitz. This supplies the finite-dimensional
Hessian differentiation without assuming higher spatial derivatives. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def fieldGaussianMomentCap (C : ℝ) : ℝ :=
  (∫ u : ℝ, 4 * Real.exp ((C + 2) * |u|) ∂gaussianReal 0 1) /
    (∫ u : ℝ, Real.exp (-C * |u|) ∂gaussianReal 0 1)

lemma quadratic_exp_envelope (C u : ℝ) :
    Real.exp (C * |u|) * (1 + |u|) ^ 2 ≤ 4 * Real.exp ((C + 2) * |u|) := by
  have h1 : 1 ≤ Real.exp |u| := Real.one_le_exp (abs_nonneg u)
  have h2 : |u| ≤ Real.exp |u| := by linarith [Real.add_one_le_exp |u|]
  have h3 : (1 + |u|) ^ 2 ≤ (2 * Real.exp |u|) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  calc
    _ ≤ Real.exp (C * |u|) * (2 * Real.exp |u|) ^ 2 :=
      mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    _ = 4 * Real.exp ((C + 2) * |u|) := by
      rw [show (C + 2) * |u| = C * |u| + (|u| + |u|) by ring,
        Real.exp_add, Real.exp_add]
      ring

theorem field_centered_tilt_second_moment {U : ℝ → ℝ}
    (hU : Measurable U) {C : ℝ}
    (hUb : ∀ u, |U u| ≤ C * |u|) :
    Integrable (fun u : ℝ => (1 + |u|) ^ 2) ((gaussianReal 0 1).tilted U) ∧
      (∫ u : ℝ, (1 + |u|) ^ 2 ∂(gaussianReal 0 1).tilted U) ≤ fieldGaussianMomentCap C := by
  let μ := gaussianReal 0 1
  have hexp : Integrable (fun u : ℝ => Real.exp (C * |u|)) μ := by
    simpa only [Real.norm_eq_abs] using (gaussianReal_exponentialNormMoments 0 1 C)
  have hlo : Integrable (fun u : ℝ => Real.exp (-C * |u|)) μ := by
    simpa only [Real.norm_eq_abs] using (gaussianReal_exponentialNormMoments 0 1 (-C))
  have hhi : Integrable (fun u : ℝ => 4 * Real.exp ((C + 2) * |u|)) μ := by
    simpa only [Real.norm_eq_abs] using
      ((gaussianReal_exponentialNormMoments 0 1 (C + 2)).const_mul 4)
  have hUi : Integrable (fun u => Real.exp (U u)) μ :=
    hexp.mono' hU.exp.aestronglyMeasurable (Filter.Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hUb u)))
  have hprod : Integrable (fun u => Real.exp (U u) * (1 + |u|) ^ 2) μ :=
    hhi.mono' (hU.exp.mul (by fun_prop)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact (mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr ((le_abs_self _).trans (hUb u))) (sq_nonneg _)).trans
            (quadratic_exp_envelope C u))
  have hdenpos : 0 < ∫ u : ℝ, Real.exp (-C * |u|) ∂μ :=
    integral_pos_iff_support_of_nonneg (fun u => (Real.exp_pos _).le) hlo |>.mpr
      (by simp [Function.support, Real.exp_ne_zero, μ])
  have hden : (∫ u : ℝ, Real.exp (-C * |u|) ∂μ) ≤ ∫ u, Real.exp (U u) ∂μ :=
    integral_mono hlo hUi (fun u => Real.exp_le_exp.mpr (by
      have h := (abs_le.mp (hUb u)).1
      linarith))
  have hnum : (∫ u, Real.exp (U u) * (1 + |u|) ^ 2 ∂μ) ≤
      ∫ u : ℝ, 4 * Real.exp ((C + 2) * |u|) ∂μ :=
    integral_mono hprod hhi (fun u =>
      (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr ((le_abs_self _).trans (hUb u))) (sq_nonneg _)).trans
          (quadratic_exp_envelope C u))
  constructor
  · rw [integrable_tilted_iff hUi]
    simpa only [smul_eq_mul] using hprod
  · rw [integral_tilted_eq_div]
    exact div_le_div₀ (integral_nonneg (fun u => by positivity)) hnum hdenpos hden

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldTiltedPairDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Covariance form of the derivative of an actual normalized average.
This is the two-coordinate formula used by the finite scalar recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

lemma field_tilted_integral_normalize {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (μ : Measure ℝ) (U : ℝ → ℝ)
    (B : ℝ → E) (ζ : ℝ) :
    (∫ u, B u ∂μ.tilted (fun u => ζ * U u)) =
      (∫ u, Real.exp (ζ * U u) ∂μ)⁻¹ •
        (∫ u, Real.exp (ζ * U u) • B u ∂μ) := by
  rw [integral_tilted, ← integral_smul]
  congr 1
  funext u
  rw [smul_smul]
  congr 1
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldGaussianPairDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial envelopes for differentiating the finite scalar Gaussian
recursion twice. The envelope has degree two in the single Gaussian mark. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

lemma field_mark_one_add_le_sq (u : ℝ) : 1 + |u| ≤ (1 + |u|) ^ 2 := by
  nlinarith [abs_nonneg u]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldGaussianFamilyRaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The raw two-coordinate derivative for a scalar Gaussian recursion
with affine variance and a locally uniformly linearly growing payoff. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology NNReal

namespace InvariantIsing

theorem field_gaussianFamily_raw_hasFDerivAt
    {U T X : ℝ × ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    (hU : Measurable U) (hT : Measurable T) (hX : Measurable X)
    {K L CT CX : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hg : ∀ q, q.1 ∈ I → |U q| ≤ K + L * |q.2|)
    (hCT : ∀ q, q.1 ∈ I → |T q| ≤ CT) (hCX : ∀ q, |X q| ≤ CX)
    (hd : ∀ q, q.1 ∈ I → HasFDerivAt U (pairLinear (T q) (X q)) q)
    (a v ζ : ℝ) {m V : ℝ} (hm : 0 < m)
    (hlo : ∀ t ∈ I, m ≤ a + v * t) (hhi : ∀ t ∈ I, a + v * t ≤ V)
    {p : ℝ × ℝ} (hp : p.1 ∈ I) :
    HasFDerivAt
      (fun q : ℝ × ℝ => gaussianTransform (a + v * q.1) ζ (fun y => U (q.1, y)) q.2)
      (∫ z, pairLinear (T (p.1, p.2 + Real.sqrt (a + v * p.1) * z) +
          X (p.1, p.2 + Real.sqrt (a + v * p.1) * z) *
            (v / (2 * Real.sqrt (a + v * p.1)) * z))
        (X (p.1, p.2 + Real.sqrt (a + v * p.1) * z))
        ∂(gaussianReal 0 1).tilted
          (fun z => ζ * U (p.1, p.2 + Real.sqrt (a + v * p.1) * z))) p := by
  let S : Set (ℝ × ℝ) := (Prod.fst ⁻¹' I) ∩
    (Prod.snd ⁻¹' Ioo (p.2 - 1) (p.2 + 1))
  let R := |v| / (2 * Real.sqrt m)
  let F := fun z : ℝ => K + L * (|p.2| + 1 + Real.sqrt V * |z|)
  let B := fun z : ℝ => CT + CX * (R * |z|) + CX
  let E := fun z : ℝ => Real.exp (|ζ| * F z)
  have hCX0 : 0 ≤ CX := (abs_nonneg _).trans (hCX (0, 0))
  have hCT0 : 0 ≤ CT := (abs_nonneg _).trans (hCT (p.1, 0) hp)
  have hR : 0 ≤ R := by dsimp only [R] <;> positivity
  have hS : S ∈ 𝓝 p :=
    Filter.inter_mem ((hI.preimage continuous_fst).mem_nhds hp)
      ((isOpen_Ioo.preimage continuous_snd).mem_nhds ⟨by linarith, by linarith⟩)
  have hF : Measurable F := by dsimp only [F]; fun_prop
  have hB : Measurable B := by dsimp only [B]; fun_prop
  have hFg : HasLinearGrowth F := by
    refine ⟨K + L * (|p.2| + 1), L * Real.sqrt V, by positivity, by positivity, fun z => ?_⟩
    dsimp only [F]
    rw [abs_of_nonneg (by positivity), Real.norm_eq_abs]
    exact le_of_eq (by ring)
  have hBg : HasLinearGrowth B := by
    refine ⟨CT + CX, CX * R, by positivity, by positivity, fun z => ?_⟩
    dsimp only [B]
    rw [abs_of_nonneg (by positivity), Real.norm_eq_abs]
    exact le_of_eq (by ring)
  have hEB : Integrable (fun z => E z * B z) (gaussianReal 0 1) :=
    field_exp_mul_linear_integrable 1 0 |ζ| hF hFg hB hBg
  have hBi : Integrable B (gaussianReal 0 1) := field_gaussian_linear_integrable 1 0 hB hBg
  have hbase : HasLinearGrowth (fun z => U (p.1, p.2 + Real.sqrt (a + v * p.1) * z)) := by
    refine ⟨K + L * |p.2|, L * Real.sqrt (a + v * p.1), by positivity, by positivity, fun z => ?_⟩
    calc
      _ ≤ K + L * |p.2 + Real.sqrt (a + v * p.1) * z| :=
        hg (p.1, p.2 + Real.sqrt (a + v * p.1) * z) hp
      _ ≤ K + L * (|p.2| + Real.sqrt (a + v * p.1) * |z|) := by
        apply add_le_add_right
        apply mul_le_mul_of_nonneg_left _ hL
        calc
          _ ≤ |p.2| + |Real.sqrt (a + v * p.1) * z| := abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      _ = _ := by rw [Real.norm_eq_abs]; ring
  have hbaseM : Measurable (fun z => U (p.1, p.2 + Real.sqrt (a + v * p.1) * z)) := by
    exact hU.comp (by fun_prop)
  have hi := field_gaussian_linear_integrable 1 0 hbaseM hbase
  have hexp := integrable_exp_of_linearGrowth (gaussianReal 0 1)
    (gaussianReal_exponentialNormMoments 0 1) hbaseM hbase ζ
  apply field_average_hasFDerivAt_of_envelope (gaussianReal 0 1)
    (U := fun q z => U (q.1, q.2 + Real.sqrt (a + v * q.1) * z))
    (D := fun q z => pairLinear (T (q.1, q.2 + Real.sqrt (a + v * q.1) * z) +
      X (q.1, q.2 + Real.sqrt (a + v * q.1) * z) *
        (v / (2 * Real.sqrt (a + v * q.1)) * z))
      (X (q.1, q.2 + Real.sqrt (a + v * q.1) * z)))
    hS (fun q => hU.comp (by fun_prop))
    ((measurable_pairLinear ((hT.comp (by fun_prop)).add
      ((hX.comp (by fun_prop)).mul (by fun_prop))) (hX.comp (by fun_prop))).aestronglyMeasurable)
    hi ζ hexp B E hBi hEB
  · intro q hq z
    refine (norm_pairLinear_le _ _).trans (add_le_add ?_ (hCX _))
    refine (abs_add_le _ _).trans (add_le_add (hCT _ hq.1) ?_)
    rw [abs_mul, abs_mul]
    exact mul_le_mul (hCX _)
      (mul_le_mul_of_nonneg_right (abs_div_two_sqrt_le hm (hlo q.1 hq.1) v) (abs_nonneg _))
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hCX0
  · intro q hq z
    apply Real.exp_le_exp.mpr
    have hq2 : |q.2| ≤ |p.2| + 1 := by
      have hdiff : |q.2 - p.2| ≤ 1 := abs_le.mpr ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩
      calc
        _ = |q.2 - p.2 + p.2| := by congr 1; ring
        _ ≤ |q.2 - p.2| + |p.2| := abs_add_le _ _
        _ ≤ _ := by linarith
    have hroot := Real.sqrt_le_sqrt (hhi q.1 hq.1)
    have hshift : |q.2 + Real.sqrt (a + v * q.1) * z| ≤
        |p.2| + 1 + Real.sqrt V * |z| := by
      calc
        _ ≤ |q.2| + |Real.sqrt (a + v * q.1) * z| := abs_add_le _ _
        _ = |q.2| + Real.sqrt (a + v * q.1) * |z| := by
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        _ ≤ _ := add_le_add hq2 (mul_le_mul_of_nonneg_right hroot (abs_nonneg z))
    calc
      ζ * U (q.1, q.2 + Real.sqrt (a + v * q.1) * z) ≤
          |ζ| * |U (q.1, q.2 + Real.sqrt (a + v * q.1) * z)| := by
        simpa only [abs_mul] using le_abs_self (ζ * U (q.1, q.2 + Real.sqrt (a + v * q.1) * z))
      _ ≤ |ζ| * F z := mul_le_mul_of_nonneg_left
        ((hg (q.1, q.2 + Real.sqrt (a + v * q.1) * z) hq.1).trans
          (add_le_add_right (mul_le_mul_of_nonneg_left hshift hL) K))
        (abs_nonneg ζ)
  · intro q hq z
    exact affine_gaussian_shift_hasFDerivAt hd a v z hq.1
      (hm.trans_le (hlo q.1 hq.1))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldGaussianFamilyGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gaussian generator with a varying, linearly growing scalar
payoff. This is the covariance derivative used in the finite field chain. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology NNReal

namespace InvariantIsing

theorem field_gaussianFamily_hasFDerivAt
    {U T X XX : ℝ × ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    (hU : Measurable U) (hT : Measurable T) (hX : Measurable X) (hXX : Measurable XX)
    {K L CT CX CXX : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hg : ∀ q, q.1 ∈ I → |U q| ≤ K + L * |q.2|)
    (hCT : ∀ q, q.1 ∈ I → |T q| ≤ CT) (hCX : ∀ q, |X q| ≤ CX)
    (hCXX : ∀ q, |XX q| ≤ CXX)
    (hd : ∀ q, q.1 ∈ I → HasFDerivAt U (pairLinear (T q) (X q)) q)
    (dx : ∀ t y, HasDerivAt (fun z => U (t, z)) (X (t, y)) y)
    (dxx : ∀ t y, HasDerivAt (fun z => X (t, z)) (XX (t, y)) y)
    (a v ζ : ℝ) {m V : ℝ} (hm : 0 < m)
    (hlo : ∀ t ∈ I, m ≤ a + v * t) (hhi : ∀ t ∈ I, a + v * t ≤ V)
    {p : ℝ × ℝ} (hp : p.1 ∈ I) :
    HasFDerivAt
      (fun q : ℝ × ℝ => gaussianTransform (a + v * q.1) ζ (fun y => U (q.1, y)) q.2)
      (pairLinear
        (gaussianTiltAverage (a + v * p.1) ζ (fun y => U (p.1, y)) (fun y => T (p.1, y)) p.2 +
          v / 2 * gaussianTiltAverage (a + v * p.1) ζ (fun y => U (p.1, y))
            (fun y => XX (p.1, y) + ζ * (X (p.1, y)) ^ 2) p.2)
        (gaussianTiltAverage (a + v * p.1) ζ (fun y => U (p.1, y)) (fun y => X (p.1, y)) p.2)) p := by
  let r := Real.sqrt (a + v * p.1)
  let F := fun y => U (p.1, y)
  let ν := (gaussianReal 0 1).tilted (fun z => ζ * F (p.2 + r * z))
  have hFm : Measurable F := hU.comp (by fun_prop)
  have hFg : HasLinearGrowth F := ⟨K, L, hK, hL, fun y => by
    simpa only [F, Real.norm_eq_abs] using hg (p.1, y) hp⟩
  have hshift : Measurable (fun z => F (p.2 + r * z)) := hFm.comp (by fun_prop)
  have hshiftG : HasLinearGrowth (fun z => F (p.2 + r * z)) :=
    (hFg.add_left p.2).scale_argument r
  have hExp := integrable_exp_of_linearGrowth (gaussianReal 0 1)
    (gaussianReal_exponentialNormMoments 0 1) hshift hshiftG ζ
  have : IsProbabilityMeasure ν := MeasureTheory.isProbabilityMeasure_tilted hExp
  have hT0 : Measurable (fun z => T (p.1, p.2 + r * z)) := hT.comp (by fun_prop)
  have hX0 : Measurable (fun z => X (p.1, p.2 + r * z)) := hX.comp (by fun_prop)
  have hiT : Integrable (fun z => T (p.1, p.2 + r * z)) ν :=
    Integrable.of_bound hT0.aestronglyMeasurable CT
      (ae_of_all _ fun z => by
        simpa only [Real.norm_eq_abs] using hCT (p.1, p.2 + r * z) hp)
  have hiX : Integrable (fun z => X (p.1, p.2 + r * z)) ν :=
    Integrable.of_bound hX0.aestronglyMeasurable CX
      (ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hCX _)
  have hZXg : HasLinearGrowth (fun z => z * X (p.1, p.2 + r * z)) := by
    refine ⟨0, |CX|, le_rfl, abs_nonneg _, fun z => ?_⟩
    rw [abs_mul, Real.norm_eq_abs, zero_add]
    calc
      _ ≤ |z| * |CX| := mul_le_mul_of_nonneg_left ((hCX _).trans (le_abs_self CX)) (abs_nonneg z)
      _ = _ := mul_comm _ _
  have hiZX : Integrable (fun z => z * X (p.1, p.2 + r * z)) ν := by
    apply (integrable_tilted_iff hExp _).mpr
    exact field_exp_mul_linear_integrable 1 0 ζ hshift hshiftG (measurable_id.mul hX0) hZXg
  have hefun : (fun z => T (p.1, p.2 + r * z) + X (p.1, p.2 + r * z) * (v / (2 * r) * z)) =
      fun z => T (p.1, p.2 + r * z) + (v / (2 * r)) * (z * X (p.1, p.2 + r * z)) := by
    funext z
    ring
  have hiA : Integrable
      (fun z => T (p.1, p.2 + r * z) + X (p.1, p.2 + r * z) * (v / (2 * r) * z)) ν := by
    rw [hefun]
    exact hiT.add (hiZX.const_mul _)
  have hraw := field_gaussianFamily_raw_hasFDerivAt hI hU hT hX hK hL hg hCT hCX hd
    a v ζ hm hlo hhi hp
  change HasFDerivAt _
    (∫ z, pairLinear (T (p.1, p.2 + r * z) + X (p.1, p.2 + r * z) * (v / (2 * r) * z))
      (X (p.1, p.2 + r * z)) ∂ν) p at hraw
  rw [integral_pairLinear ν hiA hiX] at hraw
  have he : (∫ z, T (p.1, p.2 + r * z) + X (p.1, p.2 + r * z) * (v / (2 * r) * z) ∂ν) =
      (∫ z, T (p.1, p.2 + r * z) ∂ν) +
        v / 2 * (∫ z, XX (p.1, p.2 + r * z) + ζ * (X (p.1, p.2 + r * z)) ^ 2 ∂ν) := by
    rw [hefun, integral_add hiT (hiZX.const_mul _), integral_const_mul]
    have hibp := field_gaussian_tilted_ibp hFm hFg
      (hX.comp (by fun_prop)) (hXX.comp (by fun_prop))
      (fun y => hCX (p.1, y)) (fun y => hCXX (p.1, y)) (dx p.1) (dxx p.1) r ζ p.2
    change (∫ z, z * X (p.1, p.2 + r * z) ∂ν) =
      r * (∫ z, XX (p.1, p.2 + r * z) + ζ * (X (p.1, p.2 + r * z)) ^ 2 ∂ν) at hibp
    rw [hibp]
    have hr : r ≠ 0 := (Real.sqrt_pos.mpr (hm.trans_le (hlo _ hp))).ne'
    field_simp [hr]
  rw [he] at hraw
  exact hraw

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldRealVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real-variance notation for the scalar recursion. Outside the
positive variance cone the existing Gaussian transform uses zero noise;
these spatial identities remain valid there as well. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma field_sqrt_toNNReal (s : ℝ) :
    Real.sqrt (Real.toNNReal s : ℝ) = Real.sqrt s := by
  rw [← Real.coe_sqrt, Real.sqrt]

lemma field_gaussianTransform_eq_operator (s ζ : ℝ) (F : ℝ → ℝ) :
    gaussianTransform s ζ F = gaussianOperator ζ (Real.toNNReal s) F := by
  funext z
  unfold gaussianTransform gaussianOperator
  rw [field_sqrt_toNNReal]
  split_ifs
  · rfl
  · ring

lemma field_gaussianTiltAverage_eq_transition (s ζ : ℝ) {F a : ℝ → ℝ}
    (hF : Measurable F) (ha : Measurable a) :
    gaussianTiltAverage s ζ F a = fieldSpinTransition ζ (Real.toNNReal s) F a := by
  funext z
  rw [fieldSpinTransition_eq_standard ζ (Real.toNNReal s) hF ha]
  unfold gaussianTiltAverage
  rw [field_sqrt_toNNReal]

lemma field_gaussianTiltAverage_bound (s ζ : ℝ) {F a : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (ha : Measurable a)
    {K : ℝ} (hK : ∀ y, |a y| ≤ K) (z : ℝ) :
    |gaussianTiltAverage s ζ F a z| ≤ K := by
  rw [field_gaussianTiltAverage_eq_transition s ζ hF ha]
  exact fieldSpinTransition_bound ζ (Real.toNNReal s) hF hG hK z

lemma field_gaussianTransform_hasDerivAt (s ζ : ℝ) {F D : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (hD : Measurable D)
    {K : ℝ} (hK : 0 ≤ K) (hDb : ∀ y, |D y| ≤ K)
    (hd : ∀ y, HasDerivAt F (D y) y) (z : ℝ) :
    HasDerivAt (gaussianTransform s ζ F) (gaussianTiltAverage s ζ F D z) z := by
  rw [field_gaussianTransform_eq_operator,
    field_gaussianTiltAverage_eq_transition s ζ hF hD]
  exact hasDerivAt_gaussianOperator ζ (Real.toNNReal s) hF hG hD hK hDb hd z

lemma field_gaussianTiltAverage_hasDerivAt (s ζ : ℝ) {F D a b : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (hD : Measurable D) (ha : Measurable a) (hb : Measurable b)
    {C M L : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hDb : ∀ y, |D y| ≤ C) (hab : ∀ y, |a y| ≤ M) (hbb : ∀ y, |b y| ≤ L)
    (hd : ∀ y, HasDerivAt F (D y) y) (had : ∀ y, HasDerivAt a (b y) y)
    (z : ℝ) :
    HasDerivAt (gaussianTiltAverage s ζ F a)
      (gaussianTiltAverage s ζ F b z + ζ *
        (gaussianTiltAverage s ζ F (fun y => a y * D y) z -
          gaussianTiltAverage s ζ F a z * gaussianTiltAverage s ζ F D z)) z := by
  have hm : Measurable (fun y => a y * D y) := ha.mul hD
  rw [field_gaussianTiltAverage_eq_transition s ζ hF ha,
    field_gaussianTiltAverage_eq_transition s ζ hF hb,
    field_gaussianTiltAverage_eq_transition s ζ hF hm,
    field_gaussianTiltAverage_eq_transition s ζ hF hD]
  exact hasDerivAt_fieldSpinTransition ζ (Real.toNNReal s) hF hG hD ha hb
    hC hM hDb hab hbb hd had z

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSmoothFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar field family carrying exactly the derivatives needed for
finite covariance-coordinate differentiation. No bound on the value is
required: bounded spatial derivative supplies its Gaussian moments. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

structure FieldSmoothFamily (I : Set ℝ) where
  U : ℝ × ℝ → ℝ
  X : ℝ × ℝ → ℝ
  XX : ℝ × ℝ → ℝ
  T : ℝ × ℝ → ℝ
  KX : ℝ
  KXX : ℝ
  KT : ℝ
  mU : Measurable U
  mX : Measurable X
  mXX : Measurable XX
  mT : Measurable T
  bX : ∀ p, |X p| ≤ KX
  bXX : ∀ p, |XX p| ≤ KXX
  bT : ∀ p, p.1 ∈ I → |T p| ≤ KT
  derivative : ∀ p, p.1 ∈ I → HasFDerivAt U (pairLinear (T p) (X p)) p
  spatial : ∀ t y, HasDerivAt (fun z => U (t, z)) (X (t, y)) y
  second : ∀ t y, HasDerivAt (fun z => X (t, z)) (XX (t, y)) y

namespace FieldSmoothFamily

variable {I : Set ℝ} (F : FieldSmoothFamily I)

lemma kx_nonneg : 0 ≤ F.KX := (abs_nonneg _).trans (F.bX (0, 0))

lemma growth (t : ℝ) : HasLinearGrowth (fun y => F.U (t, y)) :=
  field_spatial_linearGrowth F.kx_nonneg (fun y => F.bX (t, y)) (F.spatial t)

def value (a v ζ : ℝ) (p : ℝ × ℝ) : ℝ :=
  gaussianTransform (a + v * p.1) ζ (fun y => F.U (p.1, y)) p.2

def mean (a v ζ : ℝ) (p : ℝ × ℝ) : ℝ :=
  gaussianTiltAverage (a + v * p.1) ζ (fun y => F.U (p.1, y))
    (fun y => F.X (p.1, y)) p.2

def curvature (a v ζ : ℝ) (p : ℝ × ℝ) : ℝ :=
  gaussianTiltAverage (a + v * p.1) ζ (fun y => F.U (p.1, y))
    (fun y => F.XX (p.1, y)) p.2 + ζ *
      (gaussianTiltAverage (a + v * p.1) ζ (fun y => F.U (p.1, y))
        (fun y => (F.X (p.1, y)) ^ 2) p.2 - (F.mean a v ζ p) ^ 2)

def tangent (a v ζ : ℝ) (p : ℝ × ℝ) : ℝ :=
  gaussianTiltAverage (a + v * p.1) ζ (fun y => F.U (p.1, y))
    (fun y => F.T (p.1, y)) p.2 + v / 2 *
      gaussianTiltAverage (a + v * p.1) ζ (fun y => F.U (p.1, y))
        (fun y => F.XX (p.1, y) + ζ * (F.X (p.1, y)) ^ 2) p.2

lemma measurable_value (a v ζ : ℝ) : Measurable (F.value a v ζ) :=
  measurable_gaussianTransform_param (F.mU.comp (by fun_prop)) (by fun_prop) (by fun_prop) ζ

lemma measurable_mean (a v ζ : ℝ) : Measurable (F.mean a v ζ) :=
  measurable_gaussianTiltAverage_param (F.mU.comp (by fun_prop))
    (F.mX.comp (by fun_prop)) (by fun_prop) (by fun_prop) ζ

lemma measurable_curvature (a v ζ : ℝ) : Measurable (F.curvature a v ζ) := by
  exact (measurable_gaussianTiltAverage_param (F.mU.comp (by fun_prop))
    (F.mXX.comp (by fun_prop)) (by fun_prop) (by fun_prop) ζ).add
      (((measurable_gaussianTiltAverage_param (F.mU.comp (by fun_prop))
        ((F.mX.pow_const 2).comp (by fun_prop)) (by fun_prop) (by fun_prop) ζ).sub
          ((F.measurable_mean a v ζ).pow_const 2)).const_mul ζ)

lemma measurable_tangent (a v ζ : ℝ) : Measurable (F.tangent a v ζ) := by
  exact (measurable_gaussianTiltAverage_param (F.mU.comp (by fun_prop))
    (F.mT.comp (by fun_prop)) (by fun_prop) (by fun_prop) ζ).add
      ((measurable_gaussianTiltAverage_param (F.mU.comp (by fun_prop))
        ((F.mXX.add ((F.mX.pow_const 2).const_mul ζ)).comp (by fun_prop))
          (by fun_prop) (by fun_prop) ζ).const_mul (v / 2))

lemma bound_mean (a v ζ : ℝ) (p : ℝ × ℝ) : |F.mean a v ζ p| ≤ F.KX :=
  field_gaussianTiltAverage_bound _ _ (F.mU.comp (by fun_prop)) (F.growth p.1)
    (F.mX.comp (by fun_prop)) (fun y => F.bX (p.1, y)) p.2

lemma bound_curvature (a v ζ : ℝ) (p : ℝ × ℝ) :
    |F.curvature a v ζ p| ≤ F.KXX + 2 * |ζ| * F.KX ^ 2 := by
  have hXX := field_gaussianTiltAverage_bound (a + v * p.1) ζ
    (F.mU.comp (by fun_prop)) (F.growth p.1) (F.mXX.comp (by fun_prop))
    (fun y => F.bXX (p.1, y)) p.2
  have hsq : ∀ y, |(F.X (p.1, y)) ^ 2| ≤ F.KX ^ 2 := fun y => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (F.bX (p.1, y)) 2
  have hsqavg := field_gaussianTiltAverage_bound (a + v * p.1) ζ
    (F.mU.comp (by fun_prop)) (F.growth p.1) ((F.mX.pow_const 2).comp (by fun_prop)) hsq p.2
  have hmean : |(F.mean a v ζ p) ^ 2| ≤ F.KX ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (F.bound_mean a v ζ p) 2
  unfold curvature
  refine (abs_add_le _ _).trans (add_le_add hXX ?_)
  rw [abs_mul]
  calc
    _ ≤ |ζ| * (|gaussianTiltAverage (a + v * p.1) ζ (fun y => F.U (p.1, y))
          (fun y => (F.X (p.1, y)) ^ 2) p.2| + |(F.mean a v ζ p) ^ 2|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg ζ)
    _ ≤ |ζ| * (F.KX ^ 2 + F.KX ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hsqavg hmean) (abs_nonneg ζ)
    _ = _ := by ring

lemma bound_tangent (a v ζ : ℝ) {p : ℝ × ℝ} (hp : p.1 ∈ I) :
    |F.tangent a v ζ p| ≤ F.KT + |v| / 2 * (F.KXX + |ζ| * F.KX ^ 2) := by
  have hT := field_gaussianTiltAverage_bound (a + v * p.1) ζ
    (F.mU.comp (by fun_prop)) (F.growth p.1) (F.mT.comp (by fun_prop))
    (fun y => F.bT (p.1, y) hp) p.2
  have hgen : ∀ y, |F.XX (p.1, y) + ζ * (F.X (p.1, y)) ^ 2| ≤
      F.KXX + |ζ| * F.KX ^ 2 :=
    bounded_generator (fun y => F.bX (p.1, y)) (fun y => F.bXX (p.1, y)) ζ
  have hQ := field_gaussianTiltAverage_bound (a + v * p.1) ζ
    (F.mU.comp (by fun_prop)) (F.growth p.1)
    ((F.mXX.add ((F.mX.pow_const 2).const_mul ζ)).comp (by fun_prop)) hgen p.2
  unfold tangent
  refine (abs_add_le _ _).trans (add_le_add hT ?_)
  rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact mul_le_mul_of_nonneg_left hQ (by positivity)

lemma spatial_value (a v ζ t y : ℝ) :
    HasDerivAt (fun z => F.value a v ζ (t, z)) (F.mean a v ζ (t, y)) y := by
  exact field_gaussianTransform_hasDerivAt (a + v * t) ζ
    (F.mU.comp (by fun_prop)) (F.growth t) (F.mX.comp (by fun_prop))
    F.kx_nonneg (fun z => F.bX (t, z)) (F.spatial t) y

lemma spatial_mean (a v ζ t y : ℝ) :
    HasDerivAt (fun z => F.mean a v ζ (t, z)) (F.curvature a v ζ (t, y)) y := by
  have h := field_gaussianTiltAverage_hasDerivAt (a + v * t) ζ
    (F := fun u => F.U (t, u)) (D := fun u => F.X (t, u))
    (a := fun u => F.X (t, u)) (b := fun u => F.XX (t, u))
    (F.mU.comp (by fun_prop)) (F.growth t) (F.mX.comp (by fun_prop))
    (F.mX.comp (by fun_prop)) (F.mXX.comp (by fun_prop)) F.kx_nonneg F.kx_nonneg
    (fun z => F.bX (t, z)) (fun z => F.bX (t, z)) (fun z => F.bXX (t, z))
    (F.spatial t) (F.second t) y
  simpa only [mean, curvature, pow_two, Function.comp_apply] using h

end FieldSmoothFamily
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

structure FieldAffineStep where
  base : ℝ
  slope : ℝ
  exponent : ℝ

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSecondFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Second-derivative data for the actual two-coordinate scalar recursion.
The first coordinate is a finite covariance variation; the second is the
scalar field. All bounds are local in the covariance coordinate. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

structure FieldSecondFamily (I : Set ℝ) extends FieldSmoothFamily I where
  TX : ℝ × ℝ → ℝ
  TT : ℝ × ℝ → ℝ
  KTX : ℝ
  KTT : ℝ
  mTX : Measurable TX
  mTT : Measurable TT
  bTX : ∀ p, p.1 ∈ I → |TX p| ≤ KTX
  bTT : ∀ p, p.1 ∈ I → |TT p| ≤ KTT
  derivativeX : ∀ p, p.1 ∈ I → HasFDerivAt X (pairLinear (TX p) (XX p)) p
  derivativeT : ∀ p, p.1 ∈ I → HasFDerivAt T (pairLinear (TT p) (TX p)) p

/-- First derivative of the square-root amplitude. -/
def fieldAmplitudeSlope (a v t : ℝ) : ℝ := v / (2 * Real.sqrt (a + v * t))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldAffineAverageDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Applying the quadratic-envelope differentiation theorem to the
actual affine Gaussian shift of a finite scalar-field family. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing
namespace FieldSmoothFamily

variable {I : Set ℝ} (F : FieldSmoothFamily I)

def affineShift (a v : ℝ) (p : ℝ × ℝ) (u : ℝ) : ℝ :=
  F.U (p.1, p.2 + Real.sqrt (a + v * p.1) * u)

def affineDifferential (a v : ℝ) (p : ℝ × ℝ) (u : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  pairLinear
    (F.T (p.1, p.2 + Real.sqrt (a + v * p.1) * u) +
      F.X (p.1, p.2 + Real.sqrt (a + v * p.1) * u) *
        (fieldAmplitudeSlope a v p.1 * u))
    (F.X (p.1, p.2 + Real.sqrt (a + v * p.1) * u))

end FieldSmoothFamily
end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldAffineMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial integrability under the actual affine-noise law. These
bounds remain uniform when the spatial bias changes. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

lemma field_integrable_of_quadratic_bound (ν : Measure ℝ)
    (hq : Integrable (fun u : ℝ => (1 + |u|) ^ 2) ν)
    {A : ℝ → ℝ} (hA : Measurable A) (C : ℝ)
    (hB : ∀ u, |A u| ≤ C * (1 + |u|) ^ 2) : Integrable A ν := by
  apply (hq.const_mul C).mono' hA.aestronglyMeasurable
  exact ae_of_all _ fun u => by simpa only [Real.norm_eq_abs] using hB u

lemma field_integral_abs_le_quadratic_bound (ν : Measure ℝ)
    (hq : Integrable (fun u : ℝ => (1 + |u|) ^ 2) ν)
    {A : ℝ → ℝ} (hA : Measurable A) (C : ℝ)
    (hB : ∀ u, |A u| ≤ C * (1 + |u|) ^ 2) :
    |∫ u, A u ∂ν| ≤ C * ∫ u : ℝ, (1 + |u|) ^ 2 ∂ν := by
  have hi := field_integrable_of_quadratic_bound ν hq hA C hB
  calc
    _ ≤ ∫ u, |A u| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ u : ℝ, C * (1 + |u|) ^ 2 ∂ν := integral_mono hi.abs (hq.const_mul C) hB
    _ = _ := integral_const_mul _ _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldFiniteCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite covariance-coordinate differential used in the joint
height Hessian. The final coordinate is the scalar spatial field. -/

noncomputable section
open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

abbrev FieldCovariate (n : ℕ) := (Fin n → ℝ) × ℝ

def fieldFiniteLinear {n : ℕ} (A : Fin n → ℝ) (b : ℝ) : FieldCovariate n →L[ℝ] ℝ :=
  (∑ i, A i • ((ContinuousLinearMap.proj (R := ℝ) i).comp
    (ContinuousLinearMap.fst ℝ (Fin n → ℝ) ℝ))) +
    b • ContinuousLinearMap.snd ℝ (Fin n → ℝ) ℝ

@[simp] lemma fieldFiniteLinear_apply {n : ℕ} (A : Fin n → ℝ) (b : ℝ)
    (p : FieldCovariate n) : fieldFiniteLinear A b p = (∑ i, A i * p.1 i) + b * p.2 := by
  simp [fieldFiniteLinear]

lemma norm_fieldFiniteLinear_le {n : ℕ} (A : Fin n → ℝ) (b : ℝ) :
    ‖fieldFiniteLinear A b‖ ≤ (∑ i, |A i|) + |b| := by
  classical
  have hproj (i : Fin n) :
      ‖(ContinuousLinearMap.proj (R := ℝ) i).comp
        (ContinuousLinearMap.fst ℝ (Fin n → ℝ) ℝ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro p
    simpa using (norm_le_pi_norm p.1 i).trans (norm_fst_le p)
  unfold fieldFiniteLinear
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro i _
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hproj i) (abs_nonneg _)).trans_eq (mul_one _)
  · rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_snd_le ℝ (Fin n → ℝ) ℝ)
      (abs_nonneg _)).trans_eq (mul_one _)

lemma measurable_fieldFiniteLinear {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {A : Fin n → Ω → ℝ} {b : Ω → ℝ} (hA : ∀ i, Measurable (A i)) (hb : Measurable b) :
    Measurable (fun p => fieldFiniteLinear (fun i => A i p) (b p)) := by
  classical
  unfold fieldFiniteLinear
  exact (Finset.measurable_sum _ (fun i _ => (hA i).smul measurable_const)).add
    (hb.smul measurable_const)

lemma integral_fieldFiniteLinear {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {A : Fin n → Ω → ℝ} {b : Ω → ℝ}
    (hA : ∀ i, Integrable (A i) μ) (hb : Integrable b μ) :
    (∫ p, fieldFiniteLinear (fun i => A i p) (b p) ∂μ) =
      fieldFiniteLinear (fun i => ∫ p, A i p ∂μ) (∫ p, b p ∂μ) := by
  classical
  unfold fieldFiniteLinear
  rw [integral_add (integrable_finsetSum _ (fun i _ => (hA i).smul_const _))
    (hb.smul_const _), integral_finsetSum _ (fun i _ => (hA i).smul_const _)]
  simp only [integral_smul_const]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldFiniteTiltDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized Gaussian differentiation for the finite vector of field
covariance coordinates and the spatial coordinate. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

variable {n : ℕ}

/-- Derivative of the unnormalized Gaussian weight. -/
def fieldFiniteWeightDifferential (U : (FieldCovariate n) → ℝ → ℝ)
    (DU : (FieldCovariate n) → ℝ → (FieldCovariate n) →L[ℝ] ℝ) (ζ : ℝ)
    (p : FieldCovariate n) (u : ℝ) : (FieldCovariate n) →L[ℝ] ℝ :=
  Real.exp (ζ * U p u) • (ζ • DU p u)

/-- Derivative of the weighted observable. -/
def fieldFiniteObservableDifferential (U A : (FieldCovariate n) → ℝ → ℝ)
    (DU DA : (FieldCovariate n) → ℝ → (FieldCovariate n) →L[ℝ] ℝ) (ζ : ℝ)
    (p : FieldCovariate n) (u : ℝ) : (FieldCovariate n) →L[ℝ] ℝ :=
  Real.exp (ζ * U p u) • (DA p u + (ζ * A p u) • DU p u)

lemma field_finite_tiltedFamily_hasFDerivAt
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (U A : (FieldCovariate n) → ℝ → ℝ)
    (DU DA : (FieldCovariate n) → ℝ → (FieldCovariate n) →L[ℝ] ℝ)
    {p : FieldCovariate n} {S : Set (FieldCovariate n)} (hS : S ∈ 𝓝 p) (ζ : ℝ)
    (hU : ∀ q, Measurable (U q)) (hA : ∀ q, Measurable (A q))
    (hDU : AEStronglyMeasurable (DU p) μ) (hDA : AEStronglyMeasurable (DA p) μ)
    (hE : Integrable (fun u => Real.exp (ζ * U p u)) μ)
    (hEA : Integrable (fun u => Real.exp (ζ * U p u) * A p u) μ)
    (MD MN : ℝ → ℝ) (hMD : Integrable MD μ) (hMN : Integrable MN μ)
    (hDen : ∀ q ∈ S, ∀ u, ‖fieldFiniteWeightDifferential U DU ζ q u‖ ≤ MD u)
    (hNum : ∀ q ∈ S, ∀ u, ‖fieldFiniteObservableDifferential U A DU DA ζ q u‖ ≤ MN u)
    (dU : ∀ q ∈ S, ∀ u, HasFDerivAt (fun r => U r u) (DU q u) q)
    (dA : ∀ q ∈ S, ∀ u, HasFDerivAt (fun r => A r u) (DA q u) q) :
    let Z := ∫ u, Real.exp (ζ * U p u) ∂μ
    let N := ∫ u, Real.exp (ζ * U p u) * A p u ∂μ
    HasFDerivAt (fun q => ∫ u, A q u ∂μ.tilted (fun u => ζ * U q u))
      (Z⁻¹ • (∫ u, fieldFiniteObservableDifferential U A DU DA ζ p u ∂μ) -
        (N * (Z ^ 2)⁻¹) • (∫ u, fieldFiniteWeightDifferential U DU ζ p u ∂μ)) p := by
  let Z := ∫ u, Real.exp (ζ * U p u) ∂μ
  let N := ∫ u, Real.exp (ζ * U p u) * A p u ∂μ
  let DZ := ∫ u, fieldFiniteWeightDifferential U DU ζ p u ∂μ
  let DN := ∫ u, fieldFiniteObservableDifferential U A DU DA ζ p u ∂μ
  have hZD : HasFDerivAt (fun q => ∫ u, Real.exp (ζ * U q u) ∂μ) DZ p := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le hS
      (Eventually.of_forall fun q => ((hU q).const_mul ζ).exp.aestronglyMeasurable)
      hE (((hU p).const_mul ζ).exp.aestronglyMeasurable.smul (hDU.const_smul ζ))
      (ae_of_all _ fun u q hq => hDen q hq u) hMD
    exact ae_of_all _ fun u q hq => ((dU q hq u).const_mul ζ).exp
  have hND : HasFDerivAt (fun q => ∫ u, Real.exp (ζ * U q u) * A q u ∂μ) DN p := by
    have hDM : AEStronglyMeasurable (fieldFiniteObservableDifferential U A DU DA ζ p) μ :=
      ((hU p).const_mul ζ).exp.aestronglyMeasurable.smul
        (hDA.add (((hA p).const_mul ζ).aestronglyMeasurable.smul hDU))
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le hS
      (Eventually.of_forall fun q => (((hU q).const_mul ζ).exp.mul (hA q)).aestronglyMeasurable)
      hEA hDM (ae_of_all _ fun u q hq => hNum q hq u) hMN
    refine ae_of_all _ fun u q hq => ?_
    convert (((dU q hq u).const_mul ζ).exp).mul (dA q hq u) using 1
    all_goals try with_reducible_and_instances rfl
    apply ContinuousLinearMap.ext
    intro v
    simp only [fieldFiniteObservableDifferential, smul_apply,
      add_apply, smul_eq_mul]
    ring
  have hZ : Z ≠ 0 := (integral_exp_pos μ (U p) hE).ne'
  have hInv : HasFDerivAt (fun q => (∫ u, Real.exp (ζ * U q u) ∂μ)⁻¹)
      (-(Z ^ 2)⁻¹ • DZ) p := by
    refine ((hasDerivAt_inv hZ).hasFDerivAt.comp p hZD).congr_fderiv (Eq.symm ?_)
    · apply ContinuousLinearMap.ext
      intro v
      simp only [smul_apply, ContinuousLinearMap.comp_apply,
        smul_eq_mul]
      change -(Z ^ 2)⁻¹ * DZ v = DZ v * -(Z ^ 2)⁻¹
      ring
  have hquot := hND.mul hInv
  have he : (fun q => ∫ u, A q u ∂μ.tilted (fun u => ζ * U q u)) =
      fun q => (∫ u, Real.exp (ζ * U q u) * A q u ∂μ) *
        (∫ u, Real.exp (ζ * U q u) ∂μ)⁻¹ := by
    funext q
    rw [integral_tilted_eq_div, div_eq_mul_inv]
  rw [he]
  convert hquot using 1
  all_goals try with_reducible_and_instances rfl
  apply ContinuousLinearMap.ext
  intro v
  simp only [sub_apply, smul_apply,
    add_apply, smul_eq_mul]
  change Z⁻¹ * DN v - N * (Z ^ 2)⁻¹ * DZ v =
    N * (-(Z ^ 2)⁻¹ * DZ v) + Z⁻¹ * DN v
  ring

lemma field_finite_tiltedFamily_covariance_hasFDerivAt
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (U A : (FieldCovariate n) → ℝ → ℝ)
    (DU DA : (FieldCovariate n) → ℝ → (FieldCovariate n) →L[ℝ] ℝ)
    {p : FieldCovariate n} {S : Set (FieldCovariate n)} (hS : S ∈ 𝓝 p) (ζ : ℝ)
    (hU : ∀ q, Measurable (U q)) (hA : ∀ q, Measurable (A q))
    (hDU : AEStronglyMeasurable (DU p) μ) (hDA : AEStronglyMeasurable (DA p) μ)
    (hE : Integrable (fun u => Real.exp (ζ * U p u)) μ)
    (hEA : Integrable (fun u => Real.exp (ζ * U p u) * A p u) μ)
    (MD MN : ℝ → ℝ) (hMD : Integrable MD μ) (hMN : Integrable MN μ)
    (hDen : ∀ q ∈ S, ∀ u, ‖fieldFiniteWeightDifferential U DU ζ q u‖ ≤ MD u)
    (hNum : ∀ q ∈ S, ∀ u, ‖fieldFiniteObservableDifferential U A DU DA ζ q u‖ ≤ MN u)
    (dU : ∀ q ∈ S, ∀ u, HasFDerivAt (fun r => U r u) (DU q u) q)
    (dA : ∀ q ∈ S, ∀ u, HasFDerivAt (fun r => A r u) (DA q u) q) :
    HasFDerivAt (fun q => ∫ u, A q u ∂μ.tilted (fun u => ζ * U q u))
      ((∫ u, DA p u + (ζ * A p u) • DU p u
          ∂μ.tilted (fun u => ζ * U p u)) -
        (∫ u, A p u ∂μ.tilted (fun u => ζ * U p u)) •
          (∫ u, ζ • DU p u ∂μ.tilted (fun u => ζ * U p u))) p := by
  have h := field_finite_tiltedFamily_hasFDerivAt μ U A DU DA hS ζ hU hA hDU hDA
    hE hEA MD MN hMD hMN hDen hNum dU dA
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rw [field_tilted_integral_normalize, field_tilted_integral_normalize,
    field_tilted_integral_normalize]
  simp only [smul_eq_mul, fieldFiniteObservableDifferential, fieldFiniteWeightDifferential,
    pow_two, smul_smul]
  congr 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [smul_apply, smul_eq_mul]
  ring

lemma field_finite_gaussianPair_hasFDerivAt
    (U A : (FieldCovariate n) → ℝ → ℝ)
    (DU DA : (FieldCovariate n) → ℝ → (FieldCovariate n) →L[ℝ] ℝ)
    {p : FieldCovariate n} {S : Set (FieldCovariate n)} (hS : S ∈ 𝓝 p) (hpS : p ∈ S)
    (ζ C L CA CD CE : ℝ) (hCA : 0 ≤ CA) (hCD : 0 ≤ CD) (_hCE : 0 ≤ CE)
    (hU : ∀ q, Measurable (U q)) (hA : ∀ q, Measurable (A q))
    (hDU : AEStronglyMeasurable (DU p) (gaussianReal 0 1))
    (hDA : AEStronglyMeasurable (DA p) (gaussianReal 0 1))
    (hExp : ∀ q ∈ S, ∀ u, Real.exp (ζ * U q u) ≤ Real.exp (C + L * |u|))
    (hAb : ∀ q ∈ S, ∀ u, |A q u| ≤ CA * (1 + |u|))
    (hDb : ∀ q ∈ S, ∀ u, ‖DU q u‖ ≤ CD * (1 + |u|))
    (hEb : ∀ q ∈ S, ∀ u, ‖DA q u‖ ≤ CE * (1 + |u|) ^ 2)
    (dU : ∀ q ∈ S, ∀ u, HasFDerivAt (fun r => U r u) (DU q u) q)
    (dA : ∀ q ∈ S, ∀ u, HasFDerivAt (fun r => A r u) (DA q u) q) :
    HasFDerivAt (fun q => ∫ u, A q u
      ∂(gaussianReal 0 1).tilted (fun u => ζ * U q u))
      ((∫ u, DA p u + (ζ * A p u) • DU p u
          ∂(gaussianReal 0 1).tilted (fun u => ζ * U p u)) -
        (∫ u, A p u ∂(gaussianReal 0 1).tilted (fun u => ζ * U p u)) •
          (∫ u, ζ • DU p u ∂(gaussianReal 0 1).tilted (fun u => ζ * U p u))) p := by
  let E : ℝ → ℝ := fun u => Real.exp (C + L * |u|) * (1 + |u|) ^ 2
  have hEi : Integrable E (gaussianReal 0 1) :=
    field_gaussian_quadratic_envelope_integrable C L
  have hE : Integrable (fun u => Real.exp (ζ * U p u)) (gaussianReal 0 1) := by
    apply hEi.mono' ((hU p).const_mul ζ).exp.aestronglyMeasurable
    refine ae_of_all _ fun u => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (hExp p hpS u).trans (le_mul_of_one_le_right (Real.exp_pos _).le (by
      nlinarith [abs_nonneg u]))
  have hEA : Integrable (fun u => Real.exp (ζ * U p u) * A p u)
      (gaussianReal 0 1) := by
    apply (hEi.const_mul CA).mono' (((hU p).const_mul ζ).exp.mul (hA p)).aestronglyMeasurable
    refine ae_of_all _ fun u => ?_
    change ‖Real.exp (ζ * U p u) * A p u‖ ≤ CA * E u
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (C + L * |u|) * (CA * (1 + |u|)) :=
        mul_le_mul (hExp p hpS u) (hAb p hpS u) (abs_nonneg _) (Real.exp_pos _).le
      _ ≤ Real.exp (C + L * |u|) * (CA * (1 + |u|) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (field_mark_one_add_le_sq u) hCA) (Real.exp_pos _).le
      _ = CA * E u := by dsimp only [E] <;> ring
  apply field_finite_tiltedFamily_covariance_hasFDerivAt (gaussianReal 0 1) U A DU DA
    hS ζ hU hA hDU hDA hE hEA
    (fun u => (|ζ| * CD) * E u) (fun u => (CE + |ζ| * CA * CD) * E u)
    (hEi.const_mul _) (hEi.const_mul _)
  · intro q hq u
    rw [fieldFiniteWeightDifferential, norm_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (C + L * |u|) * (|ζ| * (CD * (1 + |u|))) :=
        mul_le_mul (hExp q hq u)
          (mul_le_mul_of_nonneg_left (hDb q hq u) (abs_nonneg _))
          (by positivity) (Real.exp_pos _).le
      _ ≤ Real.exp (C + L * |u|) * (|ζ| * (CD * (1 + |u|) ^ 2)) := by
        gcongr
        exact field_mark_one_add_le_sq u
      _ = _ := by dsimp only [E] <;> ring
  · intro q hq u
    rw [fieldFiniteObservableDifferential, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have hinner : ‖DA q u + (ζ * A q u) • DU q u‖ ≤
        (CE + |ζ| * CA * CD) * (1 + |u|) ^ 2 := by
      calc
        _ ≤ ‖DA q u‖ + ‖(ζ * A q u) • DU q u‖ := norm_add_le _ _
        _ = ‖DA q u‖ + |ζ| * |A q u| * ‖DU q u‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_mul]
        _ ≤ CE * (1 + |u|) ^ 2 + |ζ| * (CA * (1 + |u|)) * (CD * (1 + |u|)) := by
          gcongr
          · exact hEb q hq u
          · exact hAb q hq u
          · exact hDb q hq u
        _ = _ := by ring
    calc
      _ ≤ Real.exp (C + L * |u|) * ((CE + |ζ| * CA * CD) * (1 + |u|) ^ 2) :=
        mul_le_mul (hExp q hq u) hinner (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := by dsimp only [E] <;> ring
  · exact dU
  · exact dA


lemma field_finite_average_hasFDerivAt_of_envelope
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (U : (FieldCovariate n) → ℝ → ℝ) (D : (FieldCovariate n) → ℝ → (FieldCovariate n) →L[ℝ] ℝ)
    {p : FieldCovariate n} {S : Set (FieldCovariate n)} (hS : S ∈ 𝓝 p)
    (hU : ∀ q, Measurable (U q)) (hD : AEStronglyMeasurable (D p) μ)
    (hi : Integrable (U p) μ) (ζ : ℝ)
    (hExp : Integrable (fun u => Real.exp (ζ * U p u)) μ)
    (B E : ℝ → ℝ) (hBi : Integrable B μ)
    (hEBi : Integrable (fun u => E u * B u) μ)
    (hB : ∀ q ∈ S, ∀ u, ‖D q u‖ ≤ B u)
    (hE : ∀ q ∈ S, ∀ u, Real.exp (ζ * U q u) ≤ E u)
    (hd : ∀ q ∈ S, ∀ u, HasFDerivAt (fun s => U s u) (D q u) q) :
    HasFDerivAt (fun q => if ζ = 0 then ∫ u, U q u ∂μ
        else Real.log (∫ u, Real.exp (ζ * U q u) ∂μ) / ζ)
      (∫ u, D p u ∂μ.tilted (fun u => ζ * U p u)) p := by
  by_cases hζ : ζ = 0
  · subst ζ
    simp only [ite_true, if_true, zero_mul, tilted_const]
    exact hasFDerivAt_integral_of_dominated_of_fderiv_le hS
      (Eventually.of_forall fun q => (hU q).aestronglyMeasurable) hi hD
      (ae_of_all _ fun u q hq => hB q hq u) hBi
      (ae_of_all _ fun u q hq => hd q hq u)
  · have hexp := hasFDerivAt_integral_of_dominated_of_fderiv_le hS
      (F := fun q u => Real.exp (ζ * U q u))
      (F' := fun q u => Real.exp (ζ * U q u) • (ζ • D q u))
      (Eventually.of_forall fun q => ((hU q).const_mul ζ).exp.aestronglyMeasurable)
      hExp (((hU p).const_mul ζ).exp.aestronglyMeasurable.smul (hD.const_smul ζ))
      (bound := fun u => |ζ| * (E u * B u))
      (ae_of_all _ fun u q hq => by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          norm_smul, Real.norm_eq_abs]
        calc
          _ = |ζ| * (Real.exp (ζ * U q u) * ‖D q u‖) := by ring
          _ ≤ |ζ| * (E u * B u) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul (hE q hq u) (hB q hq u) (norm_nonneg _)
                ((Real.exp_pos _).le.trans (hE q hq u))) (abs_nonneg ζ))
      (hEBi.const_mul |ζ|)
      (ae_of_all _ fun u q hq => ((hd q hq u).const_mul ζ).exp)
    have hp := IsingPerceptron.integral_exp_pos μ (U p) hExp
    have hraw : (∫ u, D p u ∂μ.tilted (fun u => ζ * U p u)) =
        (∫ u, Real.exp (ζ * U p u) ∂μ)⁻¹ •
          (∫ u, Real.exp (ζ * U p u) • D p u ∂μ) := by
      rw [integral_tilted, ← integral_smul]
      congr 1
      funext u
      rw [smul_smul]
      congr 1
      ring
    have hfactor : (∫ u, Real.exp (ζ * U p u) • (ζ • D p u) ∂μ) =
        ζ • (∫ u, Real.exp (ζ * U p u) • D p u ∂μ) := by
      rw [← integral_smul]
      congr 1
      funext u
      rw [smul_smul, smul_smul]
      congr 1
      ring
    convert (config := {transparency := .instances, preTransparency := .instances}) (hexp.log hp.ne').const_mul ζ⁻¹ using 1
    · funext q
      simp only [hζ, ite_false, if_false]
      ring
    · rw [hraw, hfactor]
      simp only [smul_smul]
      congr 1
      field_simp


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

structure FieldFiniteFamily (n : ℕ) (I : Set (Fin n → ℝ)) where
  U : FieldCovariate n → ℝ
  X : FieldCovariate n → ℝ
  XX : FieldCovariate n → ℝ
  P : Fin n → FieldCovariate n → ℝ
  PX : Fin n → FieldCovariate n → ℝ
  PP : Fin n → Fin n → FieldCovariate n → ℝ
  KX : ℝ
  KXX : ℝ
  KP : ℝ
  KPX : ℝ
  KPP : ℝ
  kx_nonneg : 0 ≤ KX
  kxx_nonneg : 0 ≤ KXX
  kp_nonneg : 0 ≤ KP
  kpx_nonneg : 0 ≤ KPX
  kpp_nonneg : 0 ≤ KPP
  mU : Measurable U
  mX : Measurable X
  mXX : Measurable XX
  mP : ∀ i, Measurable (P i)
  mPX : ∀ i, Measurable (PX i)
  mPP : ∀ i j, Measurable (PP i j)
  bX : ∀ p, p.1 ∈ I → |X p| ≤ KX
  bXX : ∀ p, p.1 ∈ I → |XX p| ≤ KXX
  bP : ∀ i p, p.1 ∈ I → |P i p| ≤ KP
  bPX : ∀ i p, p.1 ∈ I → |PX i p| ≤ KPX
  bPP : ∀ i j p, p.1 ∈ I → |PP i j p| ≤ KPP
  derivative : ∀ p, p.1 ∈ I → HasFDerivAt U (fieldFiniteLinear (fun i => P i p) (X p)) p
  derivativeX : ∀ p, p.1 ∈ I → HasFDerivAt X (fieldFiniteLinear (fun i => PX i p) (XX p)) p
  derivativeP : ∀ i p, p.1 ∈ I → HasFDerivAt (P i)
    (fieldFiniteLinear (fun j => PP i j p) (PX i p)) p
  symmetric : ∀ i j p, p.1 ∈ I → PP i j p = PP j i p

namespace FieldFiniteFamily

variable {n : ℕ} {I : Set (Fin n → ℝ)} (F : FieldFiniteFamily n I)

lemma spatial_derivative (h : Fin n → ℝ) (hh : h ∈ I) (z : ℝ) :
    HasDerivAt (fun y => F.U (h, y)) (F.X (h, z)) z := by
  have hmap : HasDerivAt (fun y : ℝ => (h, y)) ((0 : Fin n → ℝ), (1 : ℝ)) z :=
    (hasDerivAt_const z h).prodMk (hasDerivAt_id z)
  have hd := (F.derivative (h, z) hh).comp_hasDerivAt z hmap
  simpa [Function.comp_def] using hd

lemma growth (h : Fin n → ℝ) (hh : h ∈ I) : HasLinearGrowth (fun y => F.U (h, y)) :=
  field_spatial_linearGrowth F.kx_nonneg (fun y => F.bX (h, y) hh) (F.spatial_derivative h hh)

end FieldFiniteFamily

def fieldFiniteVariance {n : ℕ} (a : ℝ) (v h : Fin n → ℝ) : ℝ :=
  a + ∑ i, v i * h i

def fieldFiniteSlope {n : ℕ} (a : ℝ) (v h : Fin n → ℝ) (i : Fin n) : ℝ :=
  v i / (2 * Real.sqrt (fieldFiniteVariance a v h))

def fieldFiniteCurvature {n : ℕ} (a : ℝ) (v h : Fin n → ℝ) (i j : Fin n) : ℝ :=
  -(v i / 2) * (fieldFiniteVariance a v h)⁻¹ * fieldFiniteSlope a v h j

lemma fieldFiniteCurvature_symmetric {n : ℕ} (a : ℝ) (v h : Fin n → ℝ)
    (i j : Fin n) : fieldFiniteCurvature a v h i j = fieldFiniteCurvature a v h j i := by
  unfold fieldFiniteCurvature fieldFiniteSlope
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldFiniteShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint covariance-coordinate chain rules for a single affine
Gaussian mark. These formulas preserve the symmetric height Hessian. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma fieldFiniteVariance_hasFDerivAt {n : ℕ} (a : ℝ) (v : Fin n → ℝ)
    (p : FieldCovariate n) :
    HasFDerivAt (fun q : FieldCovariate n => fieldFiniteVariance a v q.1)
      (fieldFiniteLinear v 0) p := by
  have h := ((fieldFiniteLinear v 0).hasFDerivAt (x := p)).const_add a
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext q
  simp [fieldFiniteVariance]

lemma fieldFiniteRoot_hasFDerivAt {n : ℕ} (a : ℝ) (v : Fin n → ℝ)
    {p : FieldCovariate n} (hp : 0 < fieldFiniteVariance a v p.1) :
    HasFDerivAt (fun q : FieldCovariate n => Real.sqrt (fieldFiniteVariance a v q.1))
      ((1 / (2 * Real.sqrt (fieldFiniteVariance a v p.1))) • fieldFiniteLinear v 0) p := by
  refine ((Real.hasDerivAt_sqrt hp.ne').hasFDerivAt.comp p
    (fieldFiniteVariance_hasFDerivAt a v p)).congr_fderiv (Eq.symm ?_)
  · apply ContinuousLinearMap.ext
    intro q
    simp [mul_comm, Finset.mul_sum]

lemma field_finite_affine_shift_hasFDerivAt {n : ℕ} {I : Set (Fin n → ℝ)}
    {U : FieldCovariate n → ℝ} {A : Fin n → FieldCovariate n → ℝ}
    {B : FieldCovariate n → ℝ}
    (hd : ∀ q, q.1 ∈ I → HasFDerivAt U (fieldFiniteLinear (fun i => A i q) (B q)) q)
    (a : ℝ) (v : Fin n → ℝ) (u : ℝ) {p : FieldCovariate n}
    (hp : p.1 ∈ I) (hv : 0 < fieldFiniteVariance a v p.1) :
    HasFDerivAt (fun q : FieldCovariate n => U (q.1, q.2 + Real.sqrt (fieldFiniteVariance a v q.1) * u))
      (fieldFiniteLinear
        (fun i => A i (p.1, p.2 + Real.sqrt (fieldFiniteVariance a v p.1) * u) +
          B (p.1, p.2 + Real.sqrt (fieldFiniteVariance a v p.1) * u) *
            (fieldFiniteSlope a v p.1 i * u))
        (B (p.1, p.2 + Real.sqrt (fieldFiniteVariance a v p.1) * u))) p := by
  have hroot := fieldFiniteRoot_hasFDerivAt a v hv
  have harg := hasFDerivAt_fst.prodMk (hasFDerivAt_snd.add (hroot.mul_const u))
  have h := (hd (p.1, p.2 + Real.sqrt (fieldFiniteVariance a v p.1) * u) hp).comp p harg
  refine h.congr_fderiv (Eq.symm ?_)
  · apply ContinuousLinearMap.ext
    intro q
    simp only [fieldFiniteLinear_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, add_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', smul_apply, smul_eq_mul, fieldFiniteSlope]
    simp only [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    have hs :
        (∑ i, B (p.1, p.2 + Real.sqrt (fieldFiniteVariance a v p.1) * u) *
          (v i / (2 * Real.sqrt (fieldFiniteVariance a v p.1)) * u) * q.1 i) =
        ∑ i, B (p.1, p.2 + Real.sqrt (fieldFiniteVariance a v p.1) * u) *
          (u * (1 / (2 * Real.sqrt (fieldFiniteVariance a v p.1)) * (v i * q.1 i))) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hs]
    ring

lemma fieldFiniteSlope_hasFDerivAt {n : ℕ} (a : ℝ) (v : Fin n → ℝ) (i : Fin n)
    {p : FieldCovariate n} (hp : 0 < fieldFiniteVariance a v p.1) :
    HasFDerivAt (fun q : FieldCovariate n => fieldFiniteSlope a v q.1 i)
      (fieldFiniteLinear (fun j => fieldFiniteCurvature a v p.1 i j) 0) p := by
  have hroot := fieldFiniteRoot_hasFDerivAt a v hp
  have hi := ((hasDerivAt_inv (Real.sqrt_pos.mpr hp).ne').hasFDerivAt.comp p hroot).const_mul (v i / 2)
  convert (config := {transparency := .instances, preTransparency := .instances}) hi using 1
  · funext q
    simp only [fieldFiniteSlope, Function.comp_def]
    ring
  · apply ContinuousLinearMap.ext
    intro q
    simp only [fieldFiniteLinear_apply, ContinuousLinearMap.comp_apply,
      smul_apply, smul_eq_mul, fieldFiniteCurvature, fieldFiniteSlope,
      zero_mul, add_zero, Finset.mul_sum,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    rw [Real.sq_sqrt hp.le]
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldFiniteShiftData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The joint gradient and Hessian of an affine-noise scalar payoff. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma fieldFiniteLinear_add {n : ℕ} (A B : Fin n → ℝ) (a b : ℝ) :
    fieldFiniteLinear A a + fieldFiniteLinear B b =
      fieldFiniteLinear (fun i => A i + B i) (a + b) := by
  apply ContinuousLinearMap.ext
  intro q
  simp only [add_apply, fieldFiniteLinear_apply, add_mul, Finset.sum_add_distrib]
  ring

lemma fieldFiniteLinear_smul {n : ℕ} (c : ℝ) (A : Fin n → ℝ) (a : ℝ) :
    c • fieldFiniteLinear A a = fieldFiniteLinear (fun i => c * A i) (c * a) := by
  apply ContinuousLinearMap.ext
  intro q
  simp only [smul_apply, fieldFiniteLinear_apply, smul_eq_mul, mul_add, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · ring

namespace FieldFiniteFamily

variable {n : ℕ} {I : Set (Fin n → ℝ)} (F : FieldFiniteFamily n I)

def shiftPoint (_F : FieldFiniteFamily n I) (a : ℝ) (v : Fin n → ℝ) (u : ℝ) (p : FieldCovariate n) : FieldCovariate n :=
  (p.1, p.2 + Real.sqrt (fieldFiniteVariance a v p.1) * u)

def shiftedMean (a : ℝ) (v : Fin n → ℝ) (u : ℝ) (p : FieldCovariate n) : ℝ :=
  F.X (F.shiftPoint a v u p)

def shiftedTangent (a : ℝ) (v : Fin n → ℝ) (i : Fin n) (u : ℝ) (p : FieldCovariate n) : ℝ :=
  F.P i (F.shiftPoint a v u p) + F.X (F.shiftPoint a v u p) * (fieldFiniteSlope a v p.1 i * u)

def shiftedMixed (a : ℝ) (v : Fin n → ℝ) (i : Fin n) (u : ℝ) (p : FieldCovariate n) : ℝ :=
  F.PX i (F.shiftPoint a v u p) + F.XX (F.shiftPoint a v u p) * (fieldFiniteSlope a v p.1 i * u)

def shiftedHessian (a : ℝ) (v : Fin n → ℝ) (i j : Fin n) (u : ℝ) (p : FieldCovariate n) : ℝ :=
  F.PP i j (F.shiftPoint a v u p) +
    F.PX i (F.shiftPoint a v u p) * (fieldFiniteSlope a v p.1 j * u) +
    F.PX j (F.shiftPoint a v u p) * (fieldFiniteSlope a v p.1 i * u) +
    F.XX (F.shiftPoint a v u p) * (fieldFiniteSlope a v p.1 i * u) * (fieldFiniteSlope a v p.1 j * u) +
    F.X (F.shiftPoint a v u p) * (fieldFiniteCurvature a v p.1 i j * u)

lemma shiftedMean_hasFDerivAt (a : ℝ) (v : Fin n → ℝ) (u : ℝ) {p : FieldCovariate n}
    (hp : p.1 ∈ I) (hv : 0 < fieldFiniteVariance a v p.1) :
    HasFDerivAt (F.shiftedMean a v u)
      (fieldFiniteLinear (fun i => F.shiftedMixed a v i u p) (F.XX (F.shiftPoint a v u p))) p :=
  field_finite_affine_shift_hasFDerivAt F.derivativeX a v u hp hv

lemma shiftedTangent_hasFDerivAt (a : ℝ) (v : Fin n → ℝ) (i : Fin n) (u : ℝ)
    {p : FieldCovariate n} (hp : p.1 ∈ I) (hv : 0 < fieldFiniteVariance a v p.1) :
    HasFDerivAt (F.shiftedTangent a v i u)
      (fieldFiniteLinear (fun j => F.shiftedHessian a v i j u p)
        (F.shiftedMixed a v i u p)) p := by
  have hP := field_finite_affine_shift_hasFDerivAt (F.derivativeP i) a v u hp hv
  have hX := F.shiftedMean_hasFDerivAt a v u hp hv
  have hc := (fieldFiniteSlope_hasFDerivAt a v i hv).mul_const u
  have h := hP.add (hX.mul hc)
  refine h.congr_fderiv (Eq.symm ?_)
  · simp only [fieldFiniteLinear_smul, fieldFiniteLinear_add]
    congr 1
    · funext j
      dsimp only [shiftedHessian, shiftedMixed, shiftedMean, shiftPoint]
      ring
    · dsimp only [shiftedMixed, shiftedMean, shiftPoint]
      ring

lemma shiftedHessian_symmetric (a : ℝ) (v : Fin n → ℝ) (i j : Fin n) (u : ℝ)
    {p : FieldCovariate n} (hp : p.1 ∈ I) :
    F.shiftedHessian a v i j u p = F.shiftedHessian a v j i u p := by
  unfold shiftedHessian
  rw [F.symmetric i j (F.shiftPoint a v u p) hp, fieldFiniteCurvature_symmetric a v p.1 i j]
  ring

end FieldFiniteFamily
end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldFiniteShiftBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform mark-polynomial bounds for joint height derivatives. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing
namespace FieldFiniteFamily

variable {n : ℕ} {I : Set (Fin n → ℝ)} (F : FieldFiniteFamily n I)

lemma shiftedTangent_bound (a : ℝ) (v : Fin n → ℝ) (i : Fin n) (u : ℝ)
    {p : FieldCovariate n} (hp : p.1 ∈ I) {R : ℝ} (hR : 0 ≤ R)
    (hc : |fieldFiniteSlope a v p.1 i| ≤ R) :
    |F.shiftedTangent a v i u p| ≤ (F.KP + F.KX * R) * (1 + |u|) := by
  have hP := F.kp_nonneg
  have hX := F.kx_nonneg
  unfold shiftedTangent
  calc
    _ ≤ |F.P i _| + |F.X _ * (fieldFiniteSlope a v p.1 i * u)| := abs_add_le _ _
    _ ≤ F.KP + F.KX * (R * |u|) := by
      rw [abs_mul, abs_mul]
      gcongr
      · exact F.bP i _ hp
      · exact F.bX _ hp
    _ ≤ _ := by nlinarith [mul_nonneg hP (abs_nonneg u), mul_nonneg hX hR]

lemma shiftedMixed_bound (a : ℝ) (v : Fin n → ℝ) (i : Fin n) (u : ℝ)
    {p : FieldCovariate n} (hp : p.1 ∈ I) {R : ℝ} (hR : 0 ≤ R)
    (hc : |fieldFiniteSlope a v p.1 i| ≤ R) :
    |F.shiftedMixed a v i u p| ≤ (F.KPX + F.KXX * R) * (1 + |u|) := by
  have hP := F.kpx_nonneg
  have hX := F.kxx_nonneg
  unfold shiftedMixed
  calc
    _ ≤ |F.PX i _| + |F.XX _ * (fieldFiniteSlope a v p.1 i * u)| := abs_add_le _ _
    _ ≤ F.KPX + F.KXX * (R * |u|) := by
      rw [abs_mul, abs_mul]
      gcongr
      · exact F.bPX i _ hp
      · exact F.bXX _ hp
    _ ≤ _ := by nlinarith [mul_nonneg hP (abs_nonneg u), mul_nonneg hX hR]

lemma shiftedHessian_bound (a : ℝ) (v : Fin n → ℝ) (i j : Fin n) (u : ℝ)
    {p : FieldCovariate n} (hp : p.1 ∈ I) {R D : ℝ} (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hci : |fieldFiniteSlope a v p.1 i| ≤ R)
    (hcj : |fieldFiniteSlope a v p.1 j| ≤ R)
    (hd : |fieldFiniteCurvature a v p.1 i j| ≤ D) :
    |F.shiftedHessian a v i j u p| ≤
      (F.KPP + 2 * F.KPX * R + F.KXX * R ^ 2 + F.KX * D) * (1 + |u|) ^ 2 := by
  have hPP := F.kpp_nonneg
  have hPX := F.kpx_nonneg
  have hXX := F.kxx_nonneg
  have hX := F.kx_nonneg
  have h1 : 1 ≤ (1 + |u|) ^ 2 := by nlinarith [abs_nonneg u]
  have hu : |u| ≤ (1 + |u|) ^ 2 := by nlinarith [sq_nonneg |u|, abs_nonneg u]
  have hu2 : |u| ^ 2 ≤ (1 + |u|) ^ 2 := by nlinarith [abs_nonneg u]
  let w := F.shiftPoint a v u p
  have hbPP := F.bPP i j w hp
  have hbPi := F.bPX i w hp
  have hbPj := F.bPX j w hp
  have hbXX := F.bXX w hp
  have hbX := F.bX w hp
  unfold shiftedHessian
  calc
    _ ≤ |F.PP i j w| + |F.PX i w * (fieldFiniteSlope a v p.1 j * u)| +
        |F.PX j w * (fieldFiniteSlope a v p.1 i * u)| +
        |F.XX w * (fieldFiniteSlope a v p.1 i * u) * (fieldFiniteSlope a v p.1 j * u)| +
        |F.X w * (fieldFiniteCurvature a v p.1 i j * u)| := by
      refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
      refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ F.KPP + F.KPX * (R * |u|) + F.KPX * (R * |u|) +
        F.KXX * (R * |u|) * (R * |u|) + F.KX * (D * |u|) := by
      simp only [abs_mul]
      gcongr
    _ = F.KPP * 1 + (2 * F.KPX * R) * |u| +
        (F.KXX * R ^ 2) * |u| ^ 2 + (F.KX * D) * |u| := by ring
    _ ≤ F.KPP * (1 + |u|) ^ 2 + (2 * F.KPX * R) * (1 + |u|) ^ 2 +
        (F.KXX * R ^ 2) * (1 + |u|) ^ 2 + (F.KX * D) * (1 + |u|) ^ 2 := by
      gcongr
    _ = _ := by ring

end FieldFiniteFamily
end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldFiniteMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform Gaussian tilted moments for the finite height family. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

lemma FieldFiniteFamily.spatial_abs_sub_le {n : ℕ} {I : Set (Fin n → ℝ)}
    (F : FieldFiniteFamily n I) (t : Fin n → ℝ) (ht : t ∈ I) (x y : ℝ) : |F.U (t, x) - F.U (t, y)| ≤ F.KX * |x - y| := by
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z (_ : z ∈ (univ : Set ℝ)) => (F.spatial_derivative t ht z).hasDerivWithinAt)
      (fun z _ => by simpa only [Real.norm_eq_abs] using F.bX (t, z) ht)
      convex_univ (mem_univ y) (mem_univ x)

lemma FieldFiniteFamily.shifted_second_moment {n : ℕ} {I : Set (Fin n → ℝ)}
    (F : FieldFiniteFamily n I) (t : Fin n → ℝ) (ht : t ∈ I) (z r ζ R : ℝ) (hr : |r| ≤ R) :
    Integrable (fun u : ℝ => (1 + |u|) ^ 2)
      ((gaussianReal 0 1).tilted (fun u => ζ * F.U (t, z + r * u))) ∧
      (∫ u : ℝ, (1 + |u|) ^ 2
        ∂(gaussianReal 0 1).tilted (fun u => ζ * F.U (t, z + r * u))) ≤
        fieldGaussianMomentCap (|ζ| * F.KX * R) := by
  let H : ℝ → ℝ := fun u => ζ * F.U (t, z + r * u)
  let U : ℝ → ℝ := fun u => H u - ζ * F.U (t, z)
  have hmH : Measurable H := (F.mU.comp (by fun_prop)).const_mul ζ
  have hmU : Measurable U := hmH.sub_const _
  have hb : ∀ u, |U u| ≤ (|ζ| * F.KX * R) * |u| := by
    intro u
    have hsp := F.spatial_abs_sub_le t ht (z + r * u) z
    have hdiff : z + r * u - z = r * u := by ring
    rw [hdiff, abs_mul] at hsp
    calc
      |U u| = |ζ| * |F.U (t, z + r * u) - F.U (t, z)| := by
        dsimp only [U, H]
        rw [← mul_sub, abs_mul]
      _ ≤ |ζ| * (F.KX * (|r| * |u|)) := mul_le_mul_of_nonneg_left hsp (abs_nonneg ζ)
      _ ≤ |ζ| * (F.KX * (R * |u|)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hr (abs_nonneg u)) F.kx_nonneg) (abs_nonneg ζ)
      _ = _ := by ring
  have hExp : Integrable (fun u => Real.exp (H u)) (gaussianReal 0 1) :=
    integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments 0 1)
      (F.mU.comp (by fun_prop)) ((F.growth t ht).add_left z |>.scale_argument r) ζ
  have hprob : IsProbabilityMeasure ((gaussianReal 0 1).tilted H) :=
    isProbabilityMeasure_tilted hExp
  have he : (gaussianReal 0 1).tilted U = (gaussianReal 0 1).tilted H := by
    have hh := tilted_tilted hExp (fun _ => -(ζ * F.U (t, z)))
    simpa only [tilted_const, Pi.add_def, sub_eq_add_neg, U] using hh.symm
  have h := field_centered_tilt_second_moment hmU hb
  rwa [he] at h


namespace FieldFiniteFamily

variable {n : ℕ} {I : Set (Fin n → ℝ)} (F : FieldFiniteFamily n I)

def affineShift (a : ℝ) (v : Fin n → ℝ) (p : FieldCovariate n) (u : ℝ) : ℝ :=
  F.U (F.shiftPoint a v u p)

def affineDifferential (a : ℝ) (v : Fin n → ℝ) (p : FieldCovariate n) (u : ℝ) :
    FieldCovariate n →L[ℝ] ℝ :=
  fieldFiniteLinear (fun i => F.shiftedTangent a v i u p) (F.shiftedMean a v u p)

def affineLaw (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) (p : FieldCovariate n) : Measure ℝ :=
  (gaussianReal 0 1).tilted (fun u => ζ * F.affineShift a v p u)

lemma affineLaw_probability (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    {p : FieldCovariate n} (hp : p.1 ∈ I) :
    IsProbabilityMeasure (F.affineLaw a v ζ p) := by
  apply isProbabilityMeasure_tilted
  exact integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments 0 1)
    (F.mU.comp (by fun_prop)) ((F.growth p.1 hp).add_left p.2 |>.scale_argument
      (Real.sqrt (fieldFiniteVariance a v p.1))) ζ

lemma affineLaw_quadratic_moment (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    {p : FieldCovariate n} (hp : p.1 ∈ I) :
    Integrable (fun u : ℝ => (1 + |u|) ^ 2) (F.affineLaw a v ζ p) ∧
      (∫ u : ℝ, (1 + |u|) ^ 2 ∂F.affineLaw a v ζ p) ≤
        fieldGaussianMomentCap (|ζ| * F.KX * Real.sqrt (fieldFiniteVariance a v p.1)) := by
  simpa only [affineLaw, affineShift, shiftPoint, abs_of_nonneg (Real.sqrt_nonneg _)] using
    F.shifted_second_moment p.1 hp p.2 (Real.sqrt (fieldFiniteVariance a v p.1)) ζ
      (Real.sqrt (fieldFiniteVariance a v p.1)) (by rw [abs_of_nonneg (Real.sqrt_nonneg _)])

def affineMomentCap (ζ V : ℝ) : ℝ :=
  1 + |fieldGaussianMomentCap (|ζ| * F.KX * Real.sqrt V)|

lemma affineMomentCap_pos (ζ V : ℝ) : 0 < F.affineMomentCap ζ V := by
  unfold affineMomentCap
  positivity

lemma affineLaw_moment_le (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    {p : FieldCovariate n} (hp : p.1 ∈ I) {V : ℝ}
    (hV : fieldFiniteVariance a v p.1 ≤ V) :
    (∫ u : ℝ, (1 + |u|) ^ 2 ∂F.affineLaw a v ζ p) ≤ F.affineMomentCap ζ V := by
  have h := F.shifted_second_moment p.1 hp p.2 (Real.sqrt (fieldFiniteVariance a v p.1)) ζ
    (Real.sqrt V) (by simpa only [abs_of_nonneg (Real.sqrt_nonneg _)] using Real.sqrt_le_sqrt hV)
  exact h.2.trans ((le_abs_self _).trans (le_add_of_nonneg_left zero_le_one))

lemma affineLaw_integral_bound (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    {p : FieldCovariate n} (hp : p.1 ∈ I) {V : ℝ}
    (hV : fieldFiniteVariance a v p.1 ≤ V) {A : ℝ → ℝ} (hA : Measurable A)
    {C : ℝ} (hC : 0 ≤ C) (hB : ∀ u, |A u| ≤ C * (1 + |u|) ^ 2) :
    |∫ u, A u ∂F.affineLaw a v ζ p| ≤ C * F.affineMomentCap ζ V :=
  (field_integral_abs_le_quadratic_bound _ (F.affineLaw_quadratic_moment a v ζ hp).1
    hA C hB).trans (mul_le_mul_of_nonneg_left (F.affineLaw_moment_le a v ζ hp hV) hC)

lemma affineLaw_linear_integrable (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    {p : FieldCovariate n} (hp : p.1 ∈ I)
    {A : ℝ → ℝ} (hA : Measurable A) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ u, |A u| ≤ C * (1 + |u|)) : Integrable A (F.affineLaw a v ζ p) := by
  apply field_integrable_of_quadratic_bound _ (F.affineLaw_quadratic_moment a v ζ hp).1 hA C
  intro u
  exact (hB u).trans (mul_le_mul_of_nonneg_left (field_mark_one_add_le_sq u) hC)

lemma affineLaw_bounded_integrable (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    {p : FieldCovariate n} (hp : p.1 ∈ I)
    {A : ℝ → ℝ} (hA : Measurable A) (C : ℝ) (hB : ∀ u, |A u| ≤ C) :
    Integrable A (F.affineLaw a v ζ p) := by
  have := F.affineLaw_probability a v ζ hp
  exact Integrable.of_bound hA.aestronglyMeasurable C
    (ae_of_all _ fun u => by simpa only [Real.norm_eq_abs] using hB u)

end FieldFiniteFamily
end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldFiniteLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A local Gaussian domination envelope for the finite vector of field
heights. Its constants are uniform over a neighborhood of the height vector
and the spatial field. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BigOperators

namespace InvariantIsing
namespace FieldFiniteFamily

variable {n : ℕ} {I : Set (Fin n → ℝ)} (F : FieldFiniteFamily n I)

lemma local_envelope (hI : IsOpen I) (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    {V R : ℝ} (hR : 0 ≤ R)
    (hhi : ∀ t ∈ I, fieldFiniteVariance a v t ≤ V)
    (hc : ∀ t ∈ I, ∀ i, |fieldFiniteSlope a v t i| ≤ R)
    {p : FieldCovariate n} (hp : p.1 ∈ I) :
    ∃ (S : Set (FieldCovariate n)) (C L CD : ℝ),
      S ∈ 𝓝 p ∧ p ∈ S ∧ (∀ q ∈ S, q.1 ∈ I) ∧ 0 ≤ CD ∧
      (∀ q ∈ S, ∀ u, Real.exp (ζ * F.affineShift a v q u) ≤ Real.exp (C + L * |u|)) ∧
      (∀ q ∈ S, ∀ u, ‖F.affineDifferential a v q u‖ ≤ CD * (1 + |u|)) := by
  have hX := F.kx_nonneg
  have hP := F.kp_nonneg
  let K := |F.U (p.1, 0)| + 1
  let C := |ζ| * (K + F.KX * (|p.2| + 1))
  let L := |ζ| * F.KX * Real.sqrt V
  let A := F.KP + F.KX * R
  let CD := (n : ℝ) * A + F.KX
  have hA : 0 ≤ A := by dsimp only [A] <;> positivity
  have hCD : 0 ≤ CD := by dsimp only [CD] <;> positivity
  have hpair : ContinuousAt (fun t : Fin n → ℝ => (t, (0 : ℝ))) p.1 :=
    continuousAt_id.prodMk continuousAt_const
  have hct : ContinuousAt (fun t : Fin n → ℝ => F.U (t, 0)) p.1 :=
    ContinuousAt.comp (f := fun t : Fin n → ℝ => (t, (0 : ℝ)))
      (x := p.1) (F.derivative (p.1, 0) hp).continuousAt hpair
  have he : ∀ᶠ t in 𝓝 p.1, |F.U (t, 0)| < K :=
    (tendsto_order.1 hct.abs).2 _ (lt_add_one _)
  have hset : {t : Fin n → ℝ | t ∈ I ∧ |F.U (t, 0)| < K} ∈ 𝓝 p.1 :=
    Filter.inter_mem (hI.mem_nhds hp) he
  obtain ⟨J, hJsub, hJopen, hpJ⟩ := mem_nhds_iff.mp hset
  let S : Set (FieldCovariate n) := (Prod.fst ⁻¹' J) ∩
    (Prod.snd ⁻¹' Ioo (p.2 - 1) (p.2 + 1))
  have hS : S ∈ 𝓝 p :=
    Filter.inter_mem ((hJopen.preimage continuous_fst).mem_nhds hpJ)
      ((isOpen_Ioo.preimage continuous_snd).mem_nhds ⟨by linarith, by linarith⟩)
  refine ⟨S, C, L, CD, hS, ⟨hpJ, by constructor <;> linarith⟩,
    (fun q hq => (hJsub hq.1).1), hCD, ?_, ?_⟩
  · intro q hq u
    have hqI := (hJsub hq.1).1
    have hg (y : ℝ) : |F.U (q.1, y)| ≤ K + F.KX * |y| := by
      calc
        _ = |F.U (q.1, y) - F.U (q.1, 0) + F.U (q.1, 0)| := by congr 1; ring
        _ ≤ |F.U (q.1, y) - F.U (q.1, 0)| + |F.U (q.1, 0)| := abs_add_le _ _
        _ ≤ F.KX * |y| + K := add_le_add
          (by simpa only [sub_zero] using F.spatial_abs_sub_le q.1 hqI y 0)
          (hJsub hq.1).2.le
        _ = _ := by ring
    have hq2 : |q.2| ≤ |p.2| + 1 := by
      have hh : |q.2 - p.2| ≤ 1 := abs_le.mpr ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩
      calc
        |q.2| = |q.2 - p.2 + p.2| := by congr 1; ring
        _ ≤ |q.2 - p.2| + |p.2| := abs_add_le _ _
        _ ≤ _ := by linarith
    have hshift : |q.2 + Real.sqrt (fieldFiniteVariance a v q.1) * u| ≤
        |p.2| + 1 + Real.sqrt V * |u| := by
      calc
        _ ≤ |q.2| + |Real.sqrt (fieldFiniteVariance a v q.1) * u| := abs_add_le _ _
        _ = |q.2| + Real.sqrt (fieldFiniteVariance a v q.1) * |u| := by
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        _ ≤ _ := add_le_add hq2
          (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hhi q.1 hqI)) (abs_nonneg _))
    apply Real.exp_le_exp.mpr
    calc
      ζ * F.affineShift a v q u ≤ |ζ| * |F.affineShift a v q u| := by
        simpa only [abs_mul] using le_abs_self (ζ * F.affineShift a v q u)
      _ ≤ |ζ| * (K + F.KX * |q.2 + Real.sqrt (fieldFiniteVariance a v q.1) * u|) :=
        mul_le_mul_of_nonneg_left (hg _) (abs_nonneg _)
      _ ≤ |ζ| * (K + F.KX * (|p.2| + 1 + Real.sqrt V * |u|)) := by gcongr
      _ = C + L * |u| := by dsimp only [C, L]; ring
  · intro q hq u
    have hqI := (hJsub hq.1).1
    unfold affineDifferential
    calc
      _ ≤ (∑ i, |F.shiftedTangent a v i u q|) + |F.shiftedMean a v u q| :=
        norm_fieldFiniteLinear_le _ _
      _ ≤ (∑ _i : Fin n, A * (1 + |u|)) + F.KX :=
        add_le_add (Finset.sum_le_sum (fun i _ =>
          F.shiftedTangent_bound a v i u hqI hR (hc q.1 hqI i))) (F.bX _ hqI)
      _ = (n : ℝ) * (A * (1 + |u|)) + F.KX := by simp
      _ ≤ CD * (1 + |u|) := by
        dsimp only [CD]
        nlinarith [mul_nonneg F.kx_nonneg (abs_nonneg u)]

end FieldFiniteFamily
end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldFiniteMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability of the joint finite-height Gaussian mark data. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing
namespace FieldFiniteFamily

variable {n : ℕ} {I : Set (Fin n → ℝ)} (F : FieldFiniteFamily n I)

lemma measurable_shiftedMean (a : ℝ) (v : Fin n → ℝ) (p : FieldCovariate n) :
    Measurable (fun u => F.shiftedMean a v u p) :=
  F.mX.comp (by dsimp only [shiftPoint, fieldFiniteVariance]; fun_prop)

lemma measurable_shiftedTangent (a : ℝ) (v : Fin n → ℝ) (i : Fin n) (p : FieldCovariate n) :
    Measurable (fun u => F.shiftedTangent a v i u p) := by
  exact ((F.mP i).comp (by dsimp only [shiftPoint, fieldFiniteVariance]; fun_prop)).add
    ((F.mX.comp (by dsimp only [shiftPoint, fieldFiniteVariance]; fun_prop)).mul (by fun_prop))

lemma measurable_shiftedMixed (a : ℝ) (v : Fin n → ℝ) (i : Fin n) (p : FieldCovariate n) :
    Measurable (fun u => F.shiftedMixed a v i u p) := by
  exact ((F.mPX i).comp (by dsimp only [shiftPoint, fieldFiniteVariance]; fun_prop)).add
    ((F.mXX.comp (by dsimp only [shiftPoint, fieldFiniteVariance]; fun_prop)).mul (by fun_prop))

lemma measurable_shiftedHessian (a : ℝ) (v : Fin n → ℝ) (i j : Fin n)
    (p : FieldCovariate n) : Measurable (fun u => F.shiftedHessian a v i j u p) := by
  have hm : Measurable (fun u : ℝ => F.shiftPoint a v u p) := by
    dsimp only [shiftPoint]
    fun_prop
  exact (((((F.mPP i j).comp hm).add (((F.mPX i).comp hm).mul (by fun_prop))).add
    (((F.mPX j).comp hm).mul (by fun_prop))).add
    ((((F.mXX.comp hm).mul (by fun_prop))).mul (by fun_prop))).add
    ((F.mX.comp hm).mul (by fun_prop))

lemma measurable_affineDifferential (a : ℝ) (v : Fin n → ℝ) (p : FieldCovariate n) :
    Measurable (F.affineDifferential a v p) :=
  measurable_fieldFiniteLinear (fun i => F.measurable_shiftedTangent a v i p)
    (F.measurable_shiftedMean a v p)

lemma measurable_affine_average (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    {A : FieldCovariate n → ℝ → ℝ}
    (hA : Measurable (fun p : FieldCovariate n × ℝ => A p.1 p.2)) :
    Measurable (fun p => ∫ u, A p u ∂F.affineLaw a v ζ p) := by
  have hU : Measurable (fun p : FieldCovariate n × ℝ => F.affineShift a v p.1 p.2) :=
    F.mU.comp (by dsimp only [shiftPoint, fieldFiniteVariance]; fun_prop)
  simp only [affineLaw, integral_tilted_eq_div]
  exact ((hU.const_mul ζ).exp.mul hA).stronglyMeasurable.integral_prod_right'.measurable.div
    ((hU.const_mul ζ).exp.stronglyMeasurable.integral_prod_right'.measurable)

lemma joint_measurable_shiftedMean (a : ℝ) (v : Fin n → ℝ) :
    Measurable (fun p : FieldCovariate n × ℝ => F.shiftedMean a v p.2 p.1) :=
  F.mX.comp (by dsimp only [shiftPoint, fieldFiniteVariance]; fun_prop)

lemma joint_measurable_shiftedTangent (a : ℝ) (v : Fin n → ℝ) (i : Fin n) :
    Measurable (fun p : FieldCovariate n × ℝ => F.shiftedTangent a v i p.2 p.1) := by
  exact ((F.mP i).comp (by dsimp only [shiftPoint, fieldFiniteVariance]; fun_prop)).add
    ((F.mX.comp (by dsimp only [shiftPoint, fieldFiniteVariance]; fun_prop)).mul (by
      dsimp only [fieldFiniteSlope, fieldFiniteVariance]; fun_prop))

lemma joint_measurable_shiftedMixed (a : ℝ) (v : Fin n → ℝ) (i : Fin n) :
    Measurable (fun p : FieldCovariate n × ℝ => F.shiftedMixed a v i p.2 p.1) := by
  exact ((F.mPX i).comp (by dsimp only [shiftPoint, fieldFiniteVariance]; fun_prop)).add
    ((F.mXX.comp (by dsimp only [shiftPoint, fieldFiniteVariance]; fun_prop)).mul (by
      dsimp only [fieldFiniteSlope, fieldFiniteVariance]; fun_prop))

lemma joint_measurable_shiftedHessian (a : ℝ) (v : Fin n → ℝ) (i j : Fin n) :
    Measurable (fun p : FieldCovariate n × ℝ => F.shiftedHessian a v i j p.2 p.1) := by
  have hm : Measurable (fun p : FieldCovariate n × ℝ => F.shiftPoint a v p.2 p.1) := by
    dsimp only [shiftPoint, fieldFiniteVariance]
    fun_prop
  have hs (k : Fin n) : Measurable (fun p : FieldCovariate n × ℝ =>
      fieldFiniteSlope a v p.1.1 k * p.2) := by
    dsimp only [fieldFiniteSlope, fieldFiniteVariance]
    fun_prop
  have hc : Measurable (fun p : FieldCovariate n × ℝ =>
      fieldFiniteCurvature a v p.1.1 i j * p.2) := by
    dsimp only [fieldFiniteCurvature, fieldFiniteSlope, fieldFiniteVariance]
    fun_prop
  exact (((((F.mPP i j).comp hm).add (((F.mPX i).comp hm).mul (hs j))).add
    (((F.mPX j).comp hm).mul (hs i))).add
    (((F.mXX.comp hm).mul (hs i)).mul (hs j))).add ((F.mX.comp hm).mul hc)

end FieldFiniteFamily
end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldFiniteAverageDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiation of the actual finite-height Gaussian transform and
its tilted observables. The local envelope is derived from the family. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing
namespace FieldFiniteFamily

variable {n : ℕ} {I : Set (Fin n → ℝ)} (F : FieldFiniteFamily n I)

lemma affine_average_hasFDerivAt (hI : IsOpen I)
    (A : FieldCovariate n → ℝ → ℝ)
    (DA : FieldCovariate n → ℝ → FieldCovariate n →L[ℝ] ℝ)
    (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) {V R : ℝ} (hR : 0 ≤ R)
    (hlo : ∀ t ∈ I, 0 < fieldFiniteVariance a v t)
    (hhi : ∀ t ∈ I, fieldFiniteVariance a v t ≤ V)
    (hc : ∀ t ∈ I, ∀ i, |fieldFiniteSlope a v t i| ≤ R)
    {CA CE : ℝ} (hCA : 0 ≤ CA) (hCE : 0 ≤ CE)
    (hA : ∀ q, Measurable (A q))
    (hDA : ∀ q, AEStronglyMeasurable (DA q) (gaussianReal 0 1))
    (hAb : ∀ q, q.1 ∈ I → ∀ u, |A q u| ≤ CA * (1 + |u|))
    (hEb : ∀ q, q.1 ∈ I → ∀ u, ‖DA q u‖ ≤ CE * (1 + |u|) ^ 2)
    (dA : ∀ q, q.1 ∈ I → ∀ u, HasFDerivAt (fun r => A r u) (DA q u) q)
    {p : FieldCovariate n} (hp : p.1 ∈ I) :
    HasFDerivAt (fun q => ∫ u, A q u ∂F.affineLaw a v ζ q)
      ((∫ u, DA p u + (ζ * A p u) • F.affineDifferential a v p u ∂F.affineLaw a v ζ p) -
        (∫ u, A p u ∂F.affineLaw a v ζ p) •
          (∫ u, ζ • F.affineDifferential a v p u ∂F.affineLaw a v ζ p)) p := by
  obtain ⟨S, C, L, CD, hS, hpS, hSI, hCD, hExp, hD⟩ :=
    F.local_envelope hI a v ζ hR hhi hc hp
  apply field_finite_gaussianPair_hasFDerivAt (F.affineShift a v) A
    (F.affineDifferential a v) DA hS hpS ζ C L CA CD CE hCA hCD hCE
    (fun q => F.mU.comp (by dsimp only [shiftPoint]; fun_prop)) hA
    (F.measurable_affineDifferential a v p).aestronglyMeasurable (hDA p) hExp
    (fun q hq => hAb q (hSI q hq)) hD (fun q hq => hEb q (hSI q hq))
  · intro q hq u
    exact field_finite_affine_shift_hasFDerivAt F.derivative a v u
      (hSI q hq) (hlo q.1 (hSI q hq))
  · exact fun q hq => dA q (hSI q hq)

def value (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) (p : FieldCovariate n) : ℝ :=
  gaussianTransform (fieldFiniteVariance a v p.1) ζ (fun y => F.U (p.1, y)) p.2

lemma value_hasFDerivAt (hI : IsOpen I) (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    {V R : ℝ} (hR : 0 ≤ R)
    (hlo : ∀ t ∈ I, 0 < fieldFiniteVariance a v t)
    (hhi : ∀ t ∈ I, fieldFiniteVariance a v t ≤ V)
    (hc : ∀ t ∈ I, ∀ i, |fieldFiniteSlope a v t i| ≤ R)
    {p : FieldCovariate n} (hp : p.1 ∈ I) :
    HasFDerivAt (F.value a v ζ)
      (∫ u, F.affineDifferential a v p u ∂F.affineLaw a v ζ p) p := by
  obtain ⟨S, C, L, CD, hS, _hpS, hSI, hCD, hExp, hD⟩ :=
    F.local_envelope hI a v ζ hR hhi hc hp
  let B : ℝ → ℝ := fun u => CD * (1 + |u|)
  let E : ℝ → ℝ := fun u => Real.exp (C + L * |u|)
  have hBg : HasLinearGrowth B := by
    refine ⟨CD, CD, hCD, hCD, fun u => ?_⟩
    dsimp only [B]
    rw [abs_of_nonneg (by positivity), Real.norm_eq_abs]
    exact le_of_eq (by ring)
  have hBi : Integrable B (gaussianReal 0 1) :=
    field_gaussian_linear_integrable 1 0 (by fun_prop) hBg
  have hEBi : Integrable (fun u => E u * B u) (gaussianReal 0 1) := by
    apply ((field_gaussian_quadratic_envelope_integrable C L).const_mul CD).mono' (by fun_prop)
    apply ae_of_all
    intro u
    change |Real.exp (C + L * |u|) * (CD * (1 + |u|))| ≤
      CD * (Real.exp (C + L * |u|) * (1 + |u|) ^ 2)
    rw [abs_of_nonneg (by positivity)]
    calc
      _ = CD * Real.exp (C + L * |u|) * (1 + |u|) := by ring
      _ ≤ CD * Real.exp (C + L * |u|) * (1 + |u|) ^ 2 :=
        mul_le_mul_of_nonneg_left (field_mark_one_add_le_sq u) (by positivity)
      _ = _ := by ring
  have hm : Measurable (F.affineShift a v p) := F.mU.comp (by dsimp only [shiftPoint]; fun_prop)
  have hg : HasLinearGrowth (F.affineShift a v p) :=
    (F.growth p.1 hp).add_left p.2 |>.scale_argument (Real.sqrt (fieldFiniteVariance a v p.1))
  exact field_finite_average_hasFDerivAt_of_envelope (gaussianReal 0 1)
    (F.affineShift a v) (F.affineDifferential a v) hS
    (fun q => F.mU.comp (by dsimp only [shiftPoint]; fun_prop))
    (F.measurable_affineDifferential a v p).aestronglyMeasurable
    (field_gaussian_linear_integrable 1 0 hm hg) ζ
    (integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments 0 1) hm hg ζ)
    B E hBi hEBi hD hExp (fun q hq u =>
      field_finite_affine_shift_hasFDerivAt F.derivative a v u
        (hSI q hq) (hlo q.1 (hSI q hq)))

end FieldFiniteFamily
end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldFiniteCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate form of the covariance derivative of a finite-height tilted
average. This is an identity of continuous linear maps. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma fieldFiniteLinear_sub {n : ℕ} (A B : Fin n → ℝ) (a b : ℝ) :
    fieldFiniteLinear A a - fieldFiniteLinear B b =
      fieldFiniteLinear (fun i => A i - B i) (a - b) := by
  apply ContinuousLinearMap.ext
  intro q
  simp only [sub_apply, fieldFiniteLinear_apply, sub_mul, Finset.sum_sub_distrib]
  ring

lemma field_finite_covariance {n : ℕ} (ν : Measure ℝ) (ζ : ℝ)
    (α : ℝ → ℝ) (A L : Fin n → ℝ → ℝ) (B M : ℝ → ℝ)
    (hA : ∀ i, Integrable (A i) ν) (hB : Integrable B ν)
    (hL : ∀ i, Integrable (L i) ν) (hM : Integrable M ν)
    (hαL : ∀ i, Integrable (fun u => α u * L i u) ν)
    (hαM : Integrable (fun u => α u * M u) ν) :
    (∫ u, fieldFiniteLinear (fun i => A i u) (B u) +
        (ζ * α u) • fieldFiniteLinear (fun i => L i u) (M u) ∂ν) -
      (∫ u, α u ∂ν) • (∫ u, ζ • fieldFiniteLinear (fun i => L i u) (M u) ∂ν) =
    fieldFiniteLinear
      (fun i => (∫ u, A i u ∂ν) + ζ * ((∫ u, α u * L i u ∂ν) -
        (∫ u, α u ∂ν) * (∫ u, L i u ∂ν)))
      ((∫ u, B u ∂ν) + ζ * ((∫ u, α u * M u ∂ν) -
        (∫ u, α u ∂ν) * (∫ u, M u ∂ν))) := by
  have he :
      (fun u => fieldFiniteLinear (fun i => A i u) (B u) +
        (ζ * α u) • fieldFiniteLinear (fun i => L i u) (M u)) =
      fun u => fieldFiniteLinear (fun i => A i u + ζ * (α u * L i u))
        (B u + ζ * (α u * M u)) := by
    funext u
    rw [fieldFiniteLinear_smul, fieldFiniteLinear_add]
    congr 1
    · funext i
      ring
    · ring
  have hiA (i : Fin n) : Integrable (fun u => A i u + ζ * (α u * L i u)) ν :=
    (hA i).add ((hαL i).const_mul ζ)
  have hiB : Integrable (fun u => B u + ζ * (α u * M u)) ν :=
    hB.add (hαM.const_mul ζ)
  rw [he, integral_fieldFiniteLinear ν hiA hiB, integral_smul,
    integral_fieldFiniteLinear ν hL hM, fieldFiniteLinear_smul, fieldFiniteLinear_smul,
    fieldFiniteLinear_sub]
  congr 1
  · funext i
    rw [integral_add (hA i) ((hαL i).const_mul ζ), integral_const_mul]
    ring
  · rw [integral_add hB (hαM.const_mul ζ), integral_const_mul]
    ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldFiniteCoordinateAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate form of the differentiated finite-height Gaussian average. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing
namespace FieldFiniteFamily

variable {n : ℕ} {I : Set (Fin n → ℝ)} (F : FieldFiniteFamily n I)

lemma affine_average_coordinate_derivative (hI : IsOpen I)
    (α B : FieldCovariate n → ℝ → ℝ)
    (A : Fin n → FieldCovariate n → ℝ → ℝ)
    (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) {V R : ℝ} (hR : 0 ≤ R)
    (hlo : ∀ t ∈ I, 0 < fieldFiniteVariance a v t)
    (hhi : ∀ t ∈ I, fieldFiniteVariance a v t ≤ V)
    (hc : ∀ t ∈ I, ∀ i, |fieldFiniteSlope a v t i| ≤ R)
    {CA CE : ℝ} (hCA : 0 ≤ CA) (hCE : 0 ≤ CE)
    (hα : ∀ q, Measurable (α q)) (hA : ∀ i q, Measurable (A i q))
    (hB : ∀ q, Measurable (B q))
    (bα : ∀ q, q.1 ∈ I → ∀ u, |α q u| ≤ CA * (1 + |u|))
    (bA : ∀ i q, q.1 ∈ I → ∀ u, |A i q u| ≤ CE * (1 + |u|) ^ 2)
    (bB : ∀ q, q.1 ∈ I → ∀ u, |B q u| ≤ CE * (1 + |u|) ^ 2)
    (dα : ∀ q, q.1 ∈ I → ∀ u,
      HasFDerivAt (fun r => α r u) (fieldFiniteLinear (fun i => A i q u) (B q u)) q)
    {p : FieldCovariate n} (hp : p.1 ∈ I) :
    HasFDerivAt (fun q => ∫ u, α q u ∂F.affineLaw a v ζ q)
      (fieldFiniteLinear
        (fun i => (∫ u, A i p u ∂F.affineLaw a v ζ p) + ζ *
          ((∫ u, α p u * F.shiftedTangent a v i u p ∂F.affineLaw a v ζ p) -
            (∫ u, α p u ∂F.affineLaw a v ζ p) *
              (∫ u, F.shiftedTangent a v i u p ∂F.affineLaw a v ζ p)))
        ((∫ u, B p u ∂F.affineLaw a v ζ p) + ζ *
          ((∫ u, α p u * F.shiftedMean a v u p ∂F.affineLaw a v ζ p) -
            (∫ u, α p u ∂F.affineLaw a v ζ p) *
              (∫ u, F.shiftedMean a v u p ∂F.affineLaw a v ζ p)))) p := by
  have hX := F.kx_nonneg
  have hP := F.kp_nonneg
  let DA : FieldCovariate n → ℝ → FieldCovariate n →L[ℝ] ℝ :=
    fun q u => fieldFiniteLinear (fun i => A i q u) (B q u)
  let ν := F.affineLaw a v ζ p
  have hnorm (q : FieldCovariate n) (hq : q.1 ∈ I) (u : ℝ) :
      ‖DA q u‖ ≤ ((n : ℝ) + 1) * CE * (1 + |u|) ^ 2 := by
    refine (norm_fieldFiniteLinear_le _ _).trans ?_
    calc
      _ ≤ (∑ _i : Fin n, CE * (1 + |u|) ^ 2) + CE * (1 + |u|) ^ 2 :=
        add_le_add (Finset.sum_le_sum (fun i _ => bA i q hq u)) (bB q hq u)
      _ = _ := by simp <;> ring
  have hd := F.affine_average_hasFDerivAt hI α DA a v ζ hR hlo hhi hc
    hCA (show 0 ≤ ((n : ℝ) + 1) * CE by positivity) hα
    (fun q => (measurable_fieldFiniteLinear (fun i => hA i q) (hB q)).aestronglyMeasurable)
    bα hnorm dα hp
  have hq := (F.affineLaw_quadratic_moment a v ζ hp).1
  have hiA (i : Fin n) : Integrable (A i p) ν :=
    field_integrable_of_quadratic_bound ν hq (hA i p) CE (bA i p hp)
  have hiB : Integrable (B p) ν :=
    field_integrable_of_quadratic_bound ν hq (hB p) CE (bB p hp)
  let T := F.KP + F.KX * R
  have hT : 0 ≤ T := by dsimp only [T] <;> positivity
  have bt (i : Fin n) (u : ℝ) : |F.shiftedTangent a v i u p| ≤ T * (1 + |u|) :=
    F.shiftedTangent_bound a v i u hp hR (hc p.1 hp i)
  have hiT (i : Fin n) : Integrable (fun u => F.shiftedTangent a v i u p) ν :=
    F.affineLaw_linear_integrable a v ζ hp (F.measurable_shiftedTangent a v i p) hT (bt i)
  have hiX : Integrable (fun u => F.shiftedMean a v u p) ν :=
    F.affineLaw_bounded_integrable a v ζ hp (F.measurable_shiftedMean a v p) F.KX
      (fun u => F.bX _ hp)
  have hiαT (i : Fin n) : Integrable (fun u => α p u * F.shiftedTangent a v i u p) ν := by
    apply field_integrable_of_quadratic_bound ν hq
      ((hα p).mul (F.measurable_shiftedTangent a v i p)) (CA * T)
    intro u
    change |α p u * F.shiftedTangent a v i u p| ≤ CA * T * (1 + |u|) ^ 2
    rw [abs_mul]
    calc
      _ ≤ (CA * (1 + |u|)) * (T * (1 + |u|)) :=
        mul_le_mul (bα p hp u) (bt i u) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hiαX : Integrable (fun u => α p u * F.shiftedMean a v u p) ν := by
    apply field_integrable_of_quadratic_bound ν hq
      ((hα p).mul (F.measurable_shiftedMean a v p)) (CA * F.KX)
    intro u
    change |α p u * F.shiftedMean a v u p| ≤ CA * F.KX * (1 + |u|) ^ 2
    rw [abs_mul]
    calc
      _ ≤ (CA * (1 + |u|)) * F.KX :=
        mul_le_mul (bα p hp u) (F.bX (F.shiftPoint a v u p) hp) (abs_nonneg _) (by positivity)
      _ = (CA * F.KX) * (1 + |u|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (field_mark_one_add_le_sq u) (by positivity)
  have he := field_finite_covariance ν ζ (α p) (fun i => A i p)
    (fun i u => F.shiftedTangent a v i u p) (B p) (fun u => F.shiftedMean a v u p)
    hiA hiB hiT hiX hiαT hiαX
  change ((∫ u, DA p u + (ζ * α p u) • F.affineDifferential a v p u ∂ν) -
    (∫ u, α p u ∂ν) • (∫ u, ζ • F.affineDifferential a v p u ∂ν)) = _ at he
  change HasFDerivAt _ ((∫ u, DA p u + (ζ * α p u) • F.affineDifferential a v p u ∂ν) -
    (∫ u, α p u ∂ν) • (∫ u, ζ • F.affineDifferential a v p u ∂ν)) p at hd
  rw [he] at hd
  exact hd

end FieldFiniteFamily
end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldFiniteTransformData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit joint gradient and Hessian of one finite-height Gaussian
recursion step. All expressions use the same normalized Gaussian law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing
namespace FieldFiniteFamily

variable {n : ℕ} {I : Set (Fin n → ℝ)} (F : FieldFiniteFamily n I)

def mean (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) (p : FieldCovariate n) : ℝ :=
  ∫ u, F.shiftedMean a v u p ∂F.affineLaw a v ζ p

def tangent (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) (i : Fin n) (p : FieldCovariate n) : ℝ :=
  ∫ u, F.shiftedTangent a v i u p ∂F.affineLaw a v ζ p

def curvature (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) (p : FieldCovariate n) : ℝ :=
  (∫ u, F.XX (F.shiftPoint a v u p) ∂F.affineLaw a v ζ p) + ζ *
    ((∫ u, F.shiftedMean a v u p * F.shiftedMean a v u p ∂F.affineLaw a v ζ p) -
      F.mean a v ζ p * F.mean a v ζ p)

def mixedMean (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) (i : Fin n) (p : FieldCovariate n) : ℝ :=
  (∫ u, F.shiftedMixed a v i u p ∂F.affineLaw a v ζ p) + ζ *
    ((∫ u, F.shiftedMean a v u p * F.shiftedTangent a v i u p ∂F.affineLaw a v ζ p) -
      F.mean a v ζ p * F.tangent a v ζ i p)

def secondMean (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) (i j : Fin n) (p : FieldCovariate n) : ℝ :=
  (∫ u, F.shiftedHessian a v i j u p ∂F.affineLaw a v ζ p) + ζ *
    ((∫ u, F.shiftedTangent a v i u p * F.shiftedTangent a v j u p ∂F.affineLaw a v ζ p) -
      F.tangent a v ζ i p * F.tangent a v ζ j p)

lemma secondMean_symmetric (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) (i j : Fin n)
    {p : FieldCovariate n} (hp : p.1 ∈ I) :
    F.secondMean a v ζ i j p = F.secondMean a v ζ j i p := by
  have hH : (∫ u, F.shiftedHessian a v i j u p ∂F.affineLaw a v ζ p) =
      ∫ u, F.shiftedHessian a v j i u p ∂F.affineLaw a v ζ p :=
    integral_congr_ae (ae_of_all _ fun u => F.shiftedHessian_symmetric a v i j u hp)
  have hT : (∫ u, F.shiftedTangent a v i u p * F.shiftedTangent a v j u p
      ∂F.affineLaw a v ζ p) = ∫ u, F.shiftedTangent a v j u p * F.shiftedTangent a v i u p
      ∂F.affineLaw a v ζ p := integral_congr_ae (ae_of_all _ fun u => mul_comm _ _)
  unfold secondMean
  rw [hH, hT, mul_comm (F.tangent a v ζ i p) (F.tangent a v ζ j p)]

lemma measurable_mean (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) : Measurable (F.mean a v ζ) :=
  F.measurable_affine_average a v ζ (F.joint_measurable_shiftedMean a v)

lemma measurable_tangent (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) (i : Fin n) :
    Measurable (F.tangent a v ζ i) :=
  F.measurable_affine_average a v ζ (F.joint_measurable_shiftedTangent a v i)

lemma measurable_curvature (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) :
    Measurable (F.curvature a v ζ) := by
  exact (F.measurable_affine_average a v ζ (F.mXX.comp (by dsimp only [shiftPoint, fieldFiniteVariance]; fun_prop))).add
    (((F.measurable_affine_average a v ζ ((F.joint_measurable_shiftedMean a v).mul
      (F.joint_measurable_shiftedMean a v))).sub
      ((F.measurable_mean a v ζ).mul (F.measurable_mean a v ζ))).const_mul ζ)

lemma measurable_mixedMean (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) (i : Fin n) :
    Measurable (F.mixedMean a v ζ i) := by
  exact (F.measurable_affine_average a v ζ (F.joint_measurable_shiftedMixed a v i)).add
    (((F.measurable_affine_average a v ζ ((F.joint_measurable_shiftedMean a v).mul
      (F.joint_measurable_shiftedTangent a v i))).sub
      ((F.measurable_mean a v ζ).mul (F.measurable_tangent a v ζ i))).const_mul ζ)

lemma measurable_secondMean (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) (i j : Fin n) :
    Measurable (F.secondMean a v ζ i j) := by
  exact (F.measurable_affine_average a v ζ (F.joint_measurable_shiftedHessian a v i j)).add
    (((F.measurable_affine_average a v ζ ((F.joint_measurable_shiftedTangent a v i).mul
      (F.joint_measurable_shiftedTangent a v j))).sub
      ((F.measurable_tangent a v ζ i).mul (F.measurable_tangent a v ζ j))).const_mul ζ)

end FieldFiniteFamily
end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldFiniteTransformDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint first and second derivatives of the actual finite-height
Gaussian step, with the Hessian expressed by the tilted covariance. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing
namespace FieldFiniteFamily

variable {n : ℕ} {I : Set (Fin n → ℝ)} (F : FieldFiniteFamily n I)

lemma value_coordinate_derivative (hI : IsOpen I) (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    {V R : ℝ} (hR : 0 ≤ R)
    (hlo : ∀ t ∈ I, 0 < fieldFiniteVariance a v t)
    (hhi : ∀ t ∈ I, fieldFiniteVariance a v t ≤ V)
    (hc : ∀ t ∈ I, ∀ i, |fieldFiniteSlope a v t i| ≤ R)
    {p : FieldCovariate n} (hp : p.1 ∈ I) :
    HasFDerivAt (F.value a v ζ)
      (fieldFiniteLinear (fun i => F.tangent a v ζ i p) (F.mean a v ζ p)) p := by
  have hX := F.kx_nonneg
  have hP := F.kp_nonneg
  have hD := F.value_hasFDerivAt hI a v ζ hR hlo hhi hc hp
  have hiT (i : Fin n) : Integrable (fun u => F.shiftedTangent a v i u p)
      (F.affineLaw a v ζ p) :=
    F.affineLaw_linear_integrable a v ζ hp (F.measurable_shiftedTangent a v i p)
      (by positivity : 0 ≤ F.KP + F.KX * R)
      (fun u => F.shiftedTangent_bound a v i u hp hR (hc p.1 hp i))
  have hiX : Integrable (fun u => F.shiftedMean a v u p) (F.affineLaw a v ζ p) :=
    F.affineLaw_bounded_integrable a v ζ hp (F.measurable_shiftedMean a v p) F.KX
      (fun u => F.bX _ hp)
  change HasFDerivAt _ (∫ u, fieldFiniteLinear (fun i => F.shiftedTangent a v i u p)
    (F.shiftedMean a v u p) ∂F.affineLaw a v ζ p) p at hD
  rw [integral_fieldFiniteLinear _ hiT hiX] at hD
  exact hD

lemma mean_hasFDerivAt (hI : IsOpen I) (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    {V R : ℝ} (hR : 0 ≤ R)
    (hlo : ∀ t ∈ I, 0 < fieldFiniteVariance a v t)
    (hhi : ∀ t ∈ I, fieldFiniteVariance a v t ≤ V)
    (hc : ∀ t ∈ I, ∀ i, |fieldFiniteSlope a v t i| ≤ R)
    {p : FieldCovariate n} (hp : p.1 ∈ I) :
    HasFDerivAt (F.mean a v ζ)
      (fieldFiniteLinear (fun i => F.mixedMean a v ζ i p) (F.curvature a v ζ p)) p := by
  have hX := F.kx_nonneg
  have hXX := F.kxx_nonneg
  have hP := F.kp_nonneg
  have hPX := F.kpx_nonneg
  have hPP := F.kpp_nonneg
  let B := F.KPX + F.KXX * R
  have hB : 0 ≤ B := by dsimp only [B] <;> positivity
  exact F.affine_average_coordinate_derivative hI
    (fun q u => F.shiftedMean a v u q)
    (fun q u => F.XX (F.shiftPoint a v u q))
    (fun i q u => F.shiftedMixed a v i u q) a v ζ hR hlo hhi hc
    F.kx_nonneg (show 0 ≤ B + F.KXX by positivity)
    (fun q => F.measurable_shiftedMean a v q)
    (fun i q => F.measurable_shiftedMixed a v i q)
    (fun q => F.mXX.comp (by dsimp only [shiftPoint]; fun_prop))
    (fun q hq u => (F.bX (F.shiftPoint a v u q) hq).trans
      (le_mul_of_one_le_right F.kx_nonneg (by linarith [abs_nonneg u])))
    (fun i q hq u => (F.shiftedMixed_bound a v i u hq hR (hc q.1 hq i)).trans (by
      calc
        _ ≤ B * (1 + |u|) ^ 2 :=
          mul_le_mul_of_nonneg_left (field_mark_one_add_le_sq u) hB
        _ ≤ (B + F.KXX) * (1 + |u|) ^ 2 := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right F.kxx_nonneg) (sq_nonneg _)))
    (fun q hq u => (F.bXX (F.shiftPoint a v u q) hq).trans (by
      have hq1 : 1 ≤ (1 + |u|) ^ 2 := by nlinarith [abs_nonneg u]
      calc
        F.KXX ≤ F.KXX * (1 + |u|) ^ 2 := le_mul_of_one_le_right F.kxx_nonneg hq1
        _ ≤ (B + F.KXX) * (1 + |u|) ^ 2 := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB) (sq_nonneg _)))
    (fun q hq u => F.shiftedMean_hasFDerivAt a v u hq (hlo q.1 hq)) hp

lemma tangent_hasFDerivAt (hI : IsOpen I) (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    (i : Fin n) {V R D : ℝ} (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hlo : ∀ t ∈ I, 0 < fieldFiniteVariance a v t)
    (hhi : ∀ t ∈ I, fieldFiniteVariance a v t ≤ V)
    (hc : ∀ t ∈ I, ∀ j, |fieldFiniteSlope a v t j| ≤ R)
    (hd : ∀ t ∈ I, ∀ j k, |fieldFiniteCurvature a v t j k| ≤ D)
    {p : FieldCovariate n} (hp : p.1 ∈ I) :
    HasFDerivAt (F.tangent a v ζ i)
      (fieldFiniteLinear (fun j => F.secondMean a v ζ i j p) (F.mixedMean a v ζ i p)) p := by
  have hX := F.kx_nonneg
  have hXX := F.kxx_nonneg
  have hP := F.kp_nonneg
  have hPX := F.kpx_nonneg
  have hPP := F.kpp_nonneg
  let B := F.KPX + F.KXX * R
  let C := F.KPP + 2 * F.KPX * R + F.KXX * R ^ 2 + F.KX * D
  have hB : 0 ≤ B := by dsimp only [B] <;> positivity
  have hC : 0 ≤ C := by dsimp only [C] <;> positivity
  have h := F.affine_average_coordinate_derivative hI
    (fun q u => F.shiftedTangent a v i u q)
    (fun q u => F.shiftedMixed a v i u q)
    (fun j q u => F.shiftedHessian a v i j u q) a v ζ hR hlo hhi hc
    (show 0 ≤ F.KP + F.KX * R by positivity) (show 0 ≤ B + C by positivity)
    (fun q => F.measurable_shiftedTangent a v i q)
    (fun j q => F.measurable_shiftedHessian a v i j q)
    (fun q => F.measurable_shiftedMixed a v i q)
    (fun q hq u => F.shiftedTangent_bound a v i u hq hR (hc q.1 hq i))
    (fun j q hq u => (F.shiftedHessian_bound a v i j u hq hR hD
      (hc q.1 hq i) (hc q.1 hq j) (hd q.1 hq i j)).trans (by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact le_add_of_nonneg_left hB))
    (fun q hq u => (F.shiftedMixed_bound a v i u hq hR (hc q.1 hq i)).trans (by
      calc
        _ ≤ B * (1 + |u|) ^ 2 :=
          mul_le_mul_of_nonneg_left (field_mark_one_add_le_sq u) hB
        _ ≤ (B + C) * (1 + |u|) ^ 2 := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC) (sq_nonneg _)))
    (fun q hq u => F.shiftedTangent_hasFDerivAt a v i u hq (hlo q.1 hq)) hp
  refine h.congr_fderiv (Eq.symm ?_)
  · apply congrArg₂ (fun A B => fieldFiniteLinear A B)
    · rfl
    · unfold mixedMean mean tangent
      rw [show (fun u => F.shiftedMean a v u p * F.shiftedTangent a v i u p) =
          (fun u => F.shiftedTangent a v i u p * F.shiftedMean a v u p) from
          funext (fun u => mul_comm _ _)]
      ring

end FieldFiniteFamily
end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldFiniteTransformBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform bounds on the joint gradient and Hessian after one Gaussian
step, independent of the scalar spatial field. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing
namespace FieldFiniteFamily

variable {n : ℕ} {I : Set (Fin n → ℝ)} (F : FieldFiniteFamily n I)

lemma affine_bounded_integral_bound (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    {p : FieldCovariate n} (hp : p.1 ∈ I) {A : ℝ → ℝ} {C : ℝ}
    (hA : ∀ u, |A u| ≤ C) : |∫ u, A u ∂F.affineLaw a v ζ p| ≤ C := by
  have := F.affineLaw_probability a v ζ hp
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := F.affineLaw a v ζ p) (f := A) (C := C)
      (ae_of_all _ fun u => by simpa only [Real.norm_eq_abs] using hA u)

lemma bound_mean (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    {p : FieldCovariate n} (hp : p.1 ∈ I) : |F.mean a v ζ p| ≤ F.KX :=
  F.affine_bounded_integral_bound a v ζ hp (fun u => F.bX (F.shiftPoint a v u p) hp)

lemma bound_curvature (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    {p : FieldCovariate n} (hp : p.1 ∈ I) :
    |F.curvature a v ζ p| ≤ F.KXX + 2 * |ζ| * F.KX ^ 2 := by
  have hXX := F.affine_bounded_integral_bound a v ζ hp (fun u => F.bXX (F.shiftPoint a v u p) hp)
  have hprod (u : ℝ) : |F.shiftedMean a v u p * F.shiftedMean a v u p| ≤ F.KX ^ 2 := by
    rw [abs_mul]
    simpa only [pow_two, shiftedMean] using mul_self_le_mul_self (abs_nonneg _)
      (F.bX (F.shiftPoint a v u p) hp)
  have hAvg := F.affine_bounded_integral_bound a v ζ hp hprod
  have hMean : |F.mean a v ζ p * F.mean a v ζ p| ≤ F.KX ^ 2 := by
    rw [abs_mul]
    simpa only [pow_two] using mul_self_le_mul_self (abs_nonneg _)
      (F.bound_mean a v ζ hp)
  unfold curvature
  refine (abs_add_le _ _).trans (add_le_add hXX ?_)
  rw [abs_mul]
  calc
    _ ≤ |ζ| * (F.KX ^ 2 + F.KX ^ 2) :=
      mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add hAvg hMean)) (abs_nonneg ζ)
    _ = _ := by ring

lemma affine_linear_integral_bound (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    {p : FieldCovariate n} (hp : p.1 ∈ I) {V : ℝ} (hV : fieldFiniteVariance a v p.1 ≤ V)
    {A : ℝ → ℝ} (hA : Measurable A) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ u, |A u| ≤ C * (1 + |u|)) :
    |∫ u, A u ∂F.affineLaw a v ζ p| ≤ C * F.affineMomentCap ζ V := by
  apply F.affineLaw_integral_bound a v ζ hp hV hA hC
  intro u
  exact (hB u).trans (mul_le_mul_of_nonneg_left (field_mark_one_add_le_sq u) hC)

def tangentCap (R ζ V : ℝ) : ℝ :=
  (F.KP + F.KX * R) * F.affineMomentCap ζ V

def mixedMeanCap (R ζ V : ℝ) : ℝ :=
  (F.KPX + F.KXX * R + 2 * |ζ| * F.KX * (F.KP + F.KX * R)) *
    F.affineMomentCap ζ V

def secondMeanCap (R D ζ V : ℝ) : ℝ :=
  (F.KPP + 2 * F.KPX * R + F.KXX * R ^ 2 + F.KX * D) * F.affineMomentCap ζ V +
    |ζ| * ((F.KP + F.KX * R) ^ 2 * F.affineMomentCap ζ V +
      ((F.KP + F.KX * R) * F.affineMomentCap ζ V) ^ 2)

lemma bound_tangent (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) (i : Fin n)
    {p : FieldCovariate n} (hp : p.1 ∈ I) {R V : ℝ} (hR : 0 ≤ R)
    (hc : |fieldFiniteSlope a v p.1 i| ≤ R) (hV : fieldFiniteVariance a v p.1 ≤ V) :
    |F.tangent a v ζ i p| ≤ F.tangentCap R ζ V := by
  have hX := F.kx_nonneg
  have hP := F.kp_nonneg
  exact F.affine_linear_integral_bound a v ζ hp hV
    (F.measurable_shiftedTangent a v i p) (by positivity)
    (fun u => F.shiftedTangent_bound a v i u hp hR hc)

lemma bound_mixedMean (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) (i : Fin n)
    {p : FieldCovariate n} (hp : p.1 ∈ I) {R V : ℝ} (hR : 0 ≤ R)
    (hc : |fieldFiniteSlope a v p.1 i| ≤ R) (hV : fieldFiniteVariance a v p.1 ≤ V) :
    |F.mixedMean a v ζ i p| ≤ F.mixedMeanCap R ζ V := by
  let A := F.KP + F.KX * R
  let B := F.KPX + F.KXX * R
  let M := F.affineMomentCap ζ V
  let ν := F.affineLaw a v ζ p
  have hX := F.kx_nonneg
  have hP := F.kp_nonneg
  have hXX := F.kxx_nonneg
  have hPX := F.kpx_nonneg
  have hA : 0 ≤ A := by dsimp only [A] <;> positivity
  have hB : 0 ≤ B := by dsimp only [B] <;> positivity
  have hiA : |F.tangent a v ζ i p| ≤ A * M := F.bound_tangent a v ζ i hp hR hc hV
  have hiB : |∫ u, F.shiftedMixed a v i u p ∂ν| ≤ B * M :=
    F.affine_linear_integral_bound a v ζ hp hV
      (F.measurable_shiftedMixed a v i p) hB
      (fun u => F.shiftedMixed_bound a v i u hp hR hc)
  have hiXA : |∫ u, F.shiftedMean a v u p * F.shiftedTangent a v i u p ∂ν| ≤ F.KX * A * M := by
    apply F.affine_linear_integral_bound a v ζ hp hV
      ((F.measurable_shiftedMean a v p).mul (F.measurable_shiftedTangent a v i p)) (mul_nonneg hX hA)
    intro u
    change |F.shiftedMean a v u p * F.shiftedTangent a v i u p| ≤ _
    rw [abs_mul]
    calc
      _ ≤ F.KX * (A * (1 + |u|)) := mul_le_mul (F.bX (F.shiftPoint a v u p) hp)
        (F.shiftedTangent_bound a v i u hp hR hc) (abs_nonneg _) hX
      _ = _ := by ring
  unfold mixedMean
  calc
    _ ≤ |∫ u, F.shiftedMixed a v i u p ∂ν| +
        |ζ * ((∫ u, F.shiftedMean a v u p * F.shiftedTangent a v i u p ∂ν) -
          F.mean a v ζ p * F.tangent a v ζ i p)| := abs_add_le _ _
    _ ≤ B * M + |ζ| * (F.KX * A * M + F.KX * (A * M)) := by
      apply add_le_add hiB
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg ζ)
      refine (abs_sub _ _).trans (add_le_add hiXA ?_)
      rw [abs_mul]
      exact mul_le_mul (F.bound_mean a v ζ hp) hiA (abs_nonneg _) hX
    _ = _ := by dsimp only [mixedMeanCap, A, B, M] <;> ring

lemma bound_secondMean (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) (i j : Fin n)
    {p : FieldCovariate n} (hp : p.1 ∈ I) {R D V : ℝ} (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hci : |fieldFiniteSlope a v p.1 i| ≤ R)
    (hcj : |fieldFiniteSlope a v p.1 j| ≤ R)
    (hd : |fieldFiniteCurvature a v p.1 i j| ≤ D)
    (hV : fieldFiniteVariance a v p.1 ≤ V) :
    |F.secondMean a v ζ i j p| ≤ F.secondMeanCap R D ζ V := by
  let A := F.KP + F.KX * R
  let C := F.KPP + 2 * F.KPX * R + F.KXX * R ^ 2 + F.KX * D
  let M := F.affineMomentCap ζ V
  let ν := F.affineLaw a v ζ p
  have hX := F.kx_nonneg
  have hP := F.kp_nonneg
  have hXX := F.kxx_nonneg
  have hPX := F.kpx_nonneg
  have hPP := F.kpp_nonneg
  have hA : 0 ≤ A := by dsimp only [A] <;> positivity
  have hC : 0 ≤ C := by dsimp only [C] <;> positivity
  have hM : 0 ≤ M := (F.affineMomentCap_pos ζ V).le
  have hiAi : |F.tangent a v ζ i p| ≤ A * M := F.bound_tangent a v ζ i hp hR hci hV
  have hiAj : |F.tangent a v ζ j p| ≤ A * M := F.bound_tangent a v ζ j hp hR hcj hV
  have hiC : |∫ u, F.shiftedHessian a v i j u p ∂ν| ≤ C * M :=
    F.affineLaw_integral_bound a v ζ hp hV (F.measurable_shiftedHessian a v i j p)
      hC (fun u => F.shiftedHessian_bound a v i j u hp hR hD hci hcj hd)
  have hiAA : |∫ u, F.shiftedTangent a v i u p * F.shiftedTangent a v j u p ∂ν| ≤ A ^ 2 * M := by
    apply F.affineLaw_integral_bound a v ζ hp hV
      ((F.measurable_shiftedTangent a v i p).mul (F.measurable_shiftedTangent a v j p)) (sq_nonneg A)
    intro u
    change |F.shiftedTangent a v i u p * F.shiftedTangent a v j u p| ≤ _
    rw [abs_mul]
    calc
      _ ≤ (A * (1 + |u|)) * (A * (1 + |u|)) :=
        mul_le_mul (F.shiftedTangent_bound a v i u hp hR hci)
          (F.shiftedTangent_bound a v j u hp hR hcj) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hproduct : |F.tangent a v ζ i p * F.tangent a v ζ j p| ≤ (A * M) ^ 2 := by
    rw [abs_mul]
    simpa only [pow_two] using mul_le_mul hiAi hiAj (abs_nonneg _) (mul_nonneg hA hM)
  unfold secondMean
  calc
    _ ≤ |∫ u, F.shiftedHessian a v i j u p ∂ν| +
        |ζ * ((∫ u, F.shiftedTangent a v i u p * F.shiftedTangent a v j u p ∂ν) -
          F.tangent a v ζ i p * F.tangent a v ζ j p)| := abs_add_le _ _
    _ ≤ C * M + |ζ| * (A ^ 2 * M + (A * M) ^ 2) := by
      apply add_le_add hiC
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add hiAA hproduct)) (abs_nonneg ζ)
    _ = _ := by dsimp only [secondMeanCap, A, C, M]

end FieldFiniteFamily
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
namespace FieldFiniteFamily

variable {n : ℕ} {I : Set (Fin n → ℝ)} (F : FieldFiniteFamily n I)

lemma measurable_value (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) :
    Measurable (F.value a v ζ) :=
  measurable_gaussianTransform_param (F.mU.comp (by fun_prop))
    (by dsimp only [fieldFiniteVariance]; fun_prop) measurable_snd ζ

def transform (hI : IsOpen I) (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    (V R D : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hlo : ∀ t ∈ I, 0 < fieldFiniteVariance a v t)
    (hhi : ∀ t ∈ I, fieldFiniteVariance a v t ≤ V)
    (hc : ∀ t ∈ I, ∀ i, |fieldFiniteSlope a v t i| ≤ R)
    (hd : ∀ t ∈ I, ∀ i j, |fieldFiniteCurvature a v t i j| ≤ D) : FieldFiniteFamily n I := by
  have hX := F.kx_nonneg
  have hXX := F.kxx_nonneg
  have hP := F.kp_nonneg
  have hPX := F.kpx_nonneg
  have hPP := F.kpp_nonneg
  have hM := (F.affineMomentCap_pos ζ V).le
  exact
  { U := F.value a v ζ
    X := F.mean a v ζ
    XX := F.curvature a v ζ
    P := F.tangent a v ζ
    PX := F.mixedMean a v ζ
    PP := F.secondMean a v ζ
    KX := F.KX
    KXX := F.KXX + 2 * |ζ| * F.KX ^ 2
    KP := F.tangentCap R ζ V
    KPX := F.mixedMeanCap R ζ V
    KPP := F.secondMeanCap R D ζ V
    kx_nonneg := hX
    kxx_nonneg := by positivity
    kp_nonneg := by unfold tangentCap; positivity
    kpx_nonneg := by unfold mixedMeanCap; positivity
    kpp_nonneg := by unfold secondMeanCap; positivity
    mU := F.measurable_value a v ζ
    mX := F.measurable_mean a v ζ
    mXX := F.measurable_curvature a v ζ
    mP := F.measurable_tangent a v ζ
    mPX := F.measurable_mixedMean a v ζ
    mPP := F.measurable_secondMean a v ζ
    bX := fun p hp => F.bound_mean a v ζ hp
    bXX := fun p hp => F.bound_curvature a v ζ hp
    bP := fun i p hp => F.bound_tangent a v ζ i hp hR (hc p.1 hp i) (hhi p.1 hp)
    bPX := fun i p hp => F.bound_mixedMean a v ζ i hp hR (hc p.1 hp i) (hhi p.1 hp)
    bPP := fun i j p hp => F.bound_secondMean a v ζ i j hp hR hD
      (hc p.1 hp i) (hc p.1 hp j) (hd p.1 hp i j) (hhi p.1 hp)
    derivative := fun p hp => F.value_coordinate_derivative hI a v ζ hR hlo hhi hc hp
    derivativeX := fun p hp => F.mean_hasFDerivAt hI a v ζ hR hlo hhi hc hp
    derivativeP := fun i p hp => F.tangent_hasFDerivAt hI a v ζ i hR hD hlo hhi hc hd hp
    symmetric := fun i j p hp => F.secondMean_symmetric a v ζ i j hp }

end FieldFiniteFamily

structure FieldFiniteStep (n : ℕ) where
  base : ℝ
  slope : Fin n → ℝ
  exponent : ℝ

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate charts for the exact finite field functional. The charts
use its original Gaussian increments and change a single covariance height. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

def fieldAllIncrements (h : FieldStep) : List (ℝ × ℝ≥0) :=
  List.ofFn fun i : Fin (h.depth + 1) =>
    ((fieldIncrement h i).1, NNReal.mk (fieldIncrement h i).2 (fieldIncrement_nonneg h i))

@[simp] lemma fieldAllIncrements_length (h : FieldStep) :
    (fieldAllIncrements h).length = h.depth + 1 := by simp [fieldAllIncrements]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_OverlapTestDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single diagonal of finite cavity depths works for every continuous
overlap test. Compactness is used only on the overlap interval. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped Topology BoundedContinuousFunction
namespace InvariantIsing

abbrev CompactOverlapTest := C(Icc (0 : ℝ) 1, ℝ)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLabeledProjectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint labeled spectral projectors and special axes of the physical
base model. Labels are retained even for repeated spectral values. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Matrix

namespace InvariantIsing

abbrev CavityProjectorFrame (N m d : ℕ) :=
  (Fin m → Matrix (Fin N) (Fin N) ℝ) × Matrix (Fin N) (Fin d) ℝ

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectorTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tensor features built directly from labeled spectral projectors.
They give an eigenbasis-free representation of the actual Gaussian
perturbation, with exactly its original covariance. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix NNReal

namespace InvariantIsing

abbrev CavityProjectorTensorIndex (N m : ℕ) (degree : Fin N → Fin m → ℕ) :=
  SpinTensorIndex (fun _ : Fin m => (Finset.univ : Finset (Fin N))) degree

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_CascadeSeedTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-depth vector cascade marking by independent uniform seeds. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

def cascadeSeedLaw : ProbabilityMeasure unitInterval := ⟨volume, (by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_CascadeSeedRegular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Regularity of uniform-seed trees, independent of the ancestor state. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal
namespace InvariantIsing

def CascadeSeedRegular (n : ℕ) (b : ℕ → ℝ) (T : NoiseTree unitInterval n) : Prop :=
  NoiseGibbsRegular n b (fun _ => cascadeSeedLaw)
    (fun _ (_ : PUnit × unitInterval) => 1) (fun _ _ => PUnit.unit) PUnit.unit T

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldRefineCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Splitting one interval of a finite field without changing its height. -/

noncomputable section
open IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

/-- Duplicate the old height on both sides of the new cut. -/
def fieldSplitHeight (h : FieldStep) (i : Fin (h.depth + 1))
    (j : Fin (h.depth + 2)) : ℝ :=
  if hj : j.val ≤ i.val then h.height ⟨j.val, by omega⟩
  else h.height ⟨j.val - 1, by omega⟩

lemma fieldSplitHeight_nonneg (h : FieldStep) (i : Fin (h.depth + 1))
    (j : Fin (h.depth + 2)) : 0 ≤ fieldSplitHeight h i j := by
  unfold fieldSplitHeight
  split_ifs <;> exact h.nonneg _

lemma fieldSplitHeight_monotone (h : FieldStep) (i : Fin (h.depth + 1)) :
    Monotone (fieldSplitHeight h i) := by
  intro j k hjk
  unfold fieldSplitHeight
  split_ifs <;> apply h.ordered_height <;> simp only [Fin.mk_le_mk] <;> omega

/-- Inserting a cut strictly inside one existing cell keeps the field path unchanged. -/
def fieldInsertCut (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) : FieldStep where
  depth := h.depth + 1
  cut := Fin.insertNth i.castSucc.succ c h.cut
  ordered_cut := Fin.strictMono_insertNth h.ordered_cut i c hc₀ hc₁
  first := by
    rw [Fin.insertNth_apply_below (α := fun _ => ℝ) (show (0 : Fin (h.depth + 3)) < i.castSucc.succ by
      change 0 < i.val + 1; omega)]
    exact h.first
  last := by
    rw [Fin.insertNth_apply_above (α := fun _ => ℝ)
      (show i.castSucc.succ < Fin.last (h.depth + 2) by
        change i.val + 1 < h.depth + 2; omega)]
    simpa only [eq_rec_constant, Fin.pred_last] using h.last
  height := fieldSplitHeight h i
  nonneg := fieldSplitHeight_nonneg h i
  ordered_height := fieldSplitHeight_monotone h i

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldCommonRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite common refinements, built only by duplicating constant-height cells. -/

noncomputable section
open MeasureTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

def fieldCutSet (h : FieldStep) : Finset ℝ := by
  classical
  exact Finset.univ.image h.cut

@[simp] lemma mem_fieldCutSet (h : FieldStep) (s : ℝ) :
    s ∈ fieldCutSet h ↔ ∃ i, h.cut i = s := by
  classical
  simp [fieldCutSet]

inductive FieldRefines : FieldStep → FieldStep → Prop
  | refl (h : FieldStep) : FieldRefines h h
  | insert {h k : FieldStep} (hk : FieldRefines h k) (i : Fin (k.depth + 1))
      (c : ℝ) (hc₀ : k.cut i.castSucc < c) (hc₁ : c < k.cut i.succ) :
      FieldRefines h (fieldInsertCut k i c hc₀ hc₁)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianPatternModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gaussian-pattern Hamiltonian with its diagonal self-interactions.
The array is indexed by spin coordinate first and pattern coordinate second. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
namespace InvariantIsing

def gaussianPatternCoupling {N m : ℕ} (c : ℝ) (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    Matrix (Fin N) (Fin N) ℝ :=
  (c/N) • (gaussianPatternArray z * (gaussianPatternArray z)ᵀ)

lemma gaussianPatternCoupling_isHermitian {N m : ℕ} (c : ℝ)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) : (gaussianPatternCoupling c z).IsHermitian := by
  exact (Matrix.isHermitian_mul_conjTranspose_self (gaussianPatternArray z)).smul rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianPatternRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-dimensional Gaussian orthogonal invariance and invariance of the
ordered Wishart eigenvalues, including repeated zero eigenvalues. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
namespace InvariantIsing

@[irreducible] def gaussianPatternEigenvalues {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m)) : Fin N → ℝ :=
  (gaussianPatternCoupling_isHermitian 1 z).eigenvalues

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_BilinearGaussianComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite bilinear Gaussian comparison behind the sharp rectangular upper edge. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
namespace InvariantIsing

abbrev BilinearGaussianIndex (N m : ℕ) := ((Fin N × Fin m) ⊕ Unit) ⊕ (Fin N ⊕ Fin m)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_PositiveSpectralLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Remove zero limiting weights without dropping their finite-volume labels. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology Classical BigOperators

namespace InvariantIsing

def positiveSpectralLabel {ι : Type*} (w : ι → ℝ) (fallback : {i // 0 < w i})
    (i : ι) : {i // 0 < w i} := if h : 0 < w i then ⟨i,h⟩ else fallback

lemma positiveSpectralWeights_sum {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i=1) :
    ∑ i : {i // 0 < w i}, w i=1 := by
  have hz : (∑ i : {i // ¬0 < w i}, w i)=0 := Finset.sum_eq_zero fun i _ =>
    le_antisymm (le_of_not_gt i.property) (hw i)
  have hh := Fintype.sum_subtype_add_sum_subtype (fun i => 0 < w i) w
  rw [hz,add_zero,hsum] at hh
  exact hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralPartitionIndex
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Deterministic spectral labels associated with a finite measurable
partition, allowing empty cells until zero masses are removed. -/

noncomputable section
open MeasureTheory Set
open scoped Topology Classical Function

namespace InvariantIsing

def spectralPartitionIndex {ι : Type*} (S : ι → Set ℝ)
    (hcover : ∀ x, ∃ i, x∈S i) (x : ℝ) : ι := (hcover x).choose

lemma spectralPartitionIndex_mem {ι : Type*} (S : ι → Set ℝ)
    (hcover : ∀ x, ∃ i, x∈S i) (x : ℝ) : x∈S (spectralPartitionIndex S hcover x) :=
  (hcover x).choose_spec

lemma spectralPartitionIndex_eq_iff {ι : Type*} (S : ι → Set ℝ)
    (hcover : ∀ x, ∃ i, x∈S i) (hdis : Pairwise (Disjoint on S)) (x : ℝ) (i : ι) :
    spectralPartitionIndex S hcover x=i ↔ x∈S i := by
  constructor
  · intro h
    rw [← h]
    exact spectralPartitionIndex_mem S hcover x
  · intro hx
    by_contra hne
    exact (Set.disjoint_left.mp (hdis hne)) (spectralPartitionIndex_mem S hcover x) hx

lemma measurable_spectralPartitionIndex {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    (S : ι → Set ℝ) (hcover : ∀ x, ∃ i, x∈S i) (hdis : Pairwise (Disjoint on S))
    (hS : ∀ i, MeasurableSet (S i)) : Measurable (spectralPartitionIndex S hcover) := by
  intro T _hT
  have he : (spectralPartitionIndex S hcover) ⁻¹' T=⋃ i∈T, S i := by
    ext x
    simp only [Set.mem_preimage,Set.mem_iUnion]
    constructor
    · intro hx
      exact ⟨spectralPartitionIndex S hcover x,hx,spectralPartitionIndex_mem S hcover x⟩
    · rintro ⟨i,hi,hxi⟩
      rwa [(spectralPartitionIndex_eq_iff S hcover hdis x i).mpr hxi]
  rw [he]
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hS i

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralBallPartition
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite ball cover yields a measurable partition, including a
zero-mass residual cell outside the covered spectral support. -/

noncomputable section
open MeasureTheory Set
open scoped Topology Classical Function

namespace InvariantIsing

def spectralBallCell {n : ℕ} (B : Fin n → Set ℝ) : Option (Fin n) → Set ℝ
  | none => (⋃ i, B i)ᶜ
  | some i => disjointed B i

lemma spectralBallCell_cover {n : ℕ} (B : Fin n → Set ℝ) (x : ℝ) :
    ∃ i, x∈spectralBallCell B i := by
  by_cases hx : x∈⋃ i, B i
  · rw [← iUnion_disjointed] at hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact ⟨some i,hi⟩
  · exact ⟨none,hx⟩

lemma spectralBallCell_disjoint {n : ℕ} (B : Fin n → Set ℝ) :
    Pairwise (Disjoint on spectralBallCell B) := by
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some j =>
      apply Set.disjoint_left.mpr
      intro x hx hy
      exact hx (mem_iUnion.mpr ⟨j,disjointed_subset B j hy⟩)
  | some i =>
    cases j with
    | none =>
      apply Set.disjoint_left.mpr
      intro x hx hy
      exact hy (mem_iUnion.mpr ⟨i,disjointed_subset B i hx⟩)
    | some j => exact disjoint_disjointed B (fun h => hij (congrArg some h))

lemma spectralBallCell_measurable {n : ℕ} (B : Fin n → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i)) (i : Option (Fin n)) :
    MeasurableSet (spectralBallCell B i) := by
  cases i with
  | none => exact (MeasurableSet.iUnion hB).compl
  | some i =>
    rw [spectralBallCell,disjointed_apply,Finset.sup_eq_iSup]
    exact (hB i).diff (MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => hB j)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralPartitionLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact finite spectral law produced by a measurable partition. -/

noncomputable section
open MeasureTheory Set
open scoped Topology Classical Function BigOperators

namespace InvariantIsing

lemma spectralPartitionIndex_preimage {ι : Type*} (S : ι → Set ℝ)
    (hcover : ∀ x, ∃ i, x∈S i) (hdis : Pairwise (Disjoint on S)) (i : ι) :
    (spectralPartitionIndex S hcover) ⁻¹' {i}=S i := by
  ext x
  exact spectralPartitionIndex_eq_iff S hcover hdis x i

lemma spectralPartitionWeights_sum {ι : Type*} [Fintype ι]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (S : ι → Set ℝ)
    (hcover : ∀ x, ∃ i, x∈S i) (hdis : Pairwise (Disjoint on S))
    (hS : ∀ i, MeasurableSet (S i)) : ∑ i, μ.real (S i)=1 := by
  let : MeasurableSpace ι := ⊤
  have hm := measurable_spectralPartitionIndex S hcover hdis hS
  have hh := sum_measureReal_preimage_singleton (μ := μ) Finset.univ
    (f := spectralPartitionIndex S hcover) (fun i _ => hm (measurableSet_singleton i))
  simpa only [spectralPartitionIndex_preimage S hcover hdis,Finset.coe_univ,
    Set.preimage_univ,probReal_univ] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_CompactSpectralPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite positive-mass spectral partitions for the compact-support approximation. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Metric
open scoped Topology Classical Function BigOperators

namespace InvariantIsing

def spectralBallWeight {n : ℕ} (ν : ProbabilityMeasure ℝ) (c r : Fin n → ℝ)
    (i : Option (Fin n)) : ℝ :=
  (ν : Measure ℝ).real (spectralBallCell (fun i => ball (c i) (r i)) i)

def spectralBallValue {n : ℕ} (c : Fin n → ℝ) (a : ℝ) (i : Option (Fin n)) : ℝ :=
  i.elim a c

structure CompactSpectralPartition (ν : ProbabilityMeasure ℝ) (a b δ : ℝ) where
  size : ℕ
  center : Fin size → ℝ
  radius : Fin size → ℝ
  center_mem : ∀ i, center i∈Icc a b
  radius_le : ∀ i, radius i ≤ δ
  null_boundary : ∀ i, (ν : Measure ℝ) (frontier (ball (center i) (radius i)))=0
  covers : (ν : Measure ℝ).support ⊆ ⋃ i, ball (center i) (radius i)
  lower : {i // 0 < spectralBallWeight ν center radius i}
  upper : {i // 0 < spectralBallWeight ν center radius i}
  lower_le : ∀ i : {i // 0 < spectralBallWeight ν center radius i},
    spectralBallValue center a lower ≤ spectralBallValue center a i
  le_upper : ∀ i : {i // 0 < spectralBallWeight ν center radius i},
    spectralBallValue center a i ≤ spectralBallValue center a upper

namespace CompactSpectralPartition

variable {ν : ProbabilityMeasure ℝ} {a b δ : ℝ} (D : CompactSpectralPartition ν a b δ)

def cells : Option (Fin D.size) → Set ℝ :=
  spectralBallCell (fun i => ball (D.center i) (D.radius i))

def weight : Option (Fin D.size) → ℝ := spectralBallWeight ν D.center D.radius

def value : Option (Fin D.size) → ℝ := spectralBallValue D.center a

abbrev Positive := {i // 0 < D.weight i}

lemma weight_sum : ∑ i : D.Positive, D.weight i=1 :=
  positiveSpectralWeights_sum D.weight (fun _ => measureReal_nonneg)
    (spectralPartitionWeights_sum (ν : Measure ℝ) D.cells (spectralBallCell_cover _)
      (spectralBallCell_disjoint _) (spectralBallCell_measurable _ (fun _ => measurableSet_ball)))

def law : ProbabilityMeasure ℝ :=
  ⟨finiteSpectralMeasure (fun i : D.Positive => D.weight i) (fun i => D.value i),
    finiteSpectralMeasure_probability _ _ (fun _ => measureReal_nonneg) D.weight_sum⟩

def edge : ℝ := D.value D.upper

end CompactSpectralPartition
end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_CompactPartitionPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite positive spectral partitions bracket physical mean pressure. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Classical Function

namespace InvariantIsing.CompactSpectralPartition

variable {ν : ProbabilityMeasure ℝ} {a b δ : ℝ} (D : CompactSpectralPartition ν a b δ)

def lowerValue (x : ℝ) : ℝ :=
  D.value (positiveSpectralLabel D.weight D.lower
    (spectralPartitionIndex D.cells (spectralBallCell_cover _) x))

def upperValue (x : ℝ) : ℝ :=
  D.value (positiveSpectralLabel D.weight D.upper
    (spectralPartitionIndex D.cells (spectralBallCell_cover _) x))

end InvariantIsing.CompactSpectralPartition

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_RandomSpectralBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The extreme eigenvalues control a random spectrum without moment hypotheses. -/
noncomputable section
open Filter Set
open scoped Topology
namespace InvariantIsing

def spectralRadius {n : ℕ} (eig : Fin (n+1) → ℝ) : ℝ :=
  max |spectralMinimum eig| |spectralMaximum eig|

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianPatternPublishedInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Marchenko–Pastur and Davidson–Szarek estimates for Gaussian-pattern matrices.
MP1967, Theorem1 and examples pp.459,461, gives the displayed law and empirical
limit. DS2001, TheoremII.13, gives the edge-excess and uniform-integrability
consequences for the Gaussian rectangular matrix. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
universe u
namespace InvariantIsing

/-- The edge and integrable-tail consequences of DS2001, TheoremII.13.
The rank-deficient case uses the exact zero eigenvalues of the Gram matrix. -/
structure DavidsonSzarekInput (α : ℝ) (_hα : 0 < α) : Prop where
  excess : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N))),
    (∀ N, HasLaw (Z N) (stdGaussian _) P) → ∀ c : ℝ,
    TendstoInMeasure P (fun k ω => spectralExcess
      (fun i => c*gaussianPatternEigenvalues (Z (k+1) ω) i)
      (min (c*marchenkoPasturLower α) (c*marchenkoPasturB α))
      (max (c*marchenkoPasturLower α) (c*marchenkoPasturB α))) atTop (fun _ => 0)
  uniform_integrable : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N))),
    (∀ N, HasLaw (Z N) (stdGaussian _) P) → ∀ c : ℝ,
    UniformIntegrable (fun k ω => spectralRadius
      (fun i => c*gaussianPatternEigenvalues (Z (k+1) ω) i)) 1 P

end InvariantIsing

end

end OAI
end



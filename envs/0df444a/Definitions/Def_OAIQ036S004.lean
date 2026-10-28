-- Prove2me | Definitions.Def_OAIQ036S004
-- name    : OAIQ036S004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T04:53:33.901621+00:00
-- url     : https://prove2.me/theorems/b5bee36c-7085-4b58-a327-72868d76738e
-- title:
--   Definitions bundle OAIQ036S004 of the split of OpenAI, Stretched-exponential barriers for typical SK initial states
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SK.main`, carved from OpenAI's openai/math development (OpenAI, *Stretched-exponential barriers for typical SK initial states*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 216 declarations of OpenAI's Lean: 86 definitions and 130 theorems. The definitions and types are `OAI.SK.Analytic.embeddedSiteExponent`, `OAI.SK.Analytic.energyTrim`, `OAI.SK.Analytic.enumeratedDisorder`, `OAI.SK.Analytic.extendedQuantileParisi`, `OAI.SK.Analytic.fiberGaussianDensity`, `OAI.SK.Analytic.finiteGoodEvent`, `OAI.SK.Analytic.finiteParisiInf`, `OAI.SK.Analytic.finiteParisiValues`, `OAI.SK.Analytic.gaussianResponse`, `OAI.SK.Analytic.gibbsFiniteLaw`, `OAI.SK.Analytic.hierarchyGaussianLaw`, `OAI.SK.Analytic.hierarchyJointMoment`, `OAI.SK.Analytic.hierarchyLaw`, `OAI.SK.Analytic.hierarchyLogDensity`, `OAI.SK.Analytic.hierarchyOverlapError`, `OAI.SK.Analytic.hierarchyPathLogDensity`, `OAI.SK.Analytic.hierarchyPotential`, `OAI.SK.Analytic.hierarchyReplicaSecond`, `OAI.SK.Analytic.hierarchySpinWeight`, `OAI.SK.Analytic.hierarchyTerminalGibbs`, `OAI.SK.Analytic.hierarchyTraceSquare`, `OAI.SK.Analytic.interactionSum`, `OAI.SK.Analytic.kernelEvent`, `OAI.SK.Analytic.matrixReplicaEquiv`, `OAI.SK.Analytic.narrowBaseQuadratic`, `OAI.SK.Analytic.narrowCDFTrialCoefficient`, `OAI.SK.Analytic.narrowJointMoment`, `OAI.SK.Analytic.narrowMixedMoment`, `OAI.SK.Analytic.narrowSusceptibility`, `OAI.SK.Analytic.narrowTentSquare`, `OAI.SK.Analytic.natBankDefault`, `OAI.SK.Analytic.natBankPool`, `OAI.SK.Analytic.observableCoefficientBilinear`, `OAI.SK.Analytic.observableExponent`, `OAI.SK.Analytic.occupation`, `OAI.SK.Analytic.orientedBankPool`, `OAI.SK.Analytic.orientedLockingSet`, `OAI.SK.Analytic.pairCommonHierarchy`, `OAI.SK.Analytic.pairCommonHierarchyAverage`, `OAI.SK.Analytic.pairIndependentAverage` and 46 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability/SKBarriers, in whole or in part: `SKBarriers_Calculus_CoordinateGaussianLaw`, `SKBarriers_Calculus_ParameterAlgebra`, `SKBarriers_Calculus_ParameterCalculus`, `SKBarriers_Calculus_ParameterFiniteLog`, `SKBarriers_Calculus_ParameterHierarchyMoment`, `SKBarriers_Coverage_CoverageTrimming`, `SKBarriers_Coverage_FiniteCoverageMixing`, `SKBarriers_Coverage_HighProbability`, `SKBarriers_Coverage_ThermodynamicLimit`, `SKBarriers_Dynamics_BankPool`, `SKBarriers_Dynamics_FiniteMarkovPath`, `SKBarriers_Dynamics_HeatBathEnergy`, `SKBarriers_Dynamics_KernelEvents`, `SKBarriers_Gaussian_BlockStein`, `SKBarriers_Gaussian_ExponentialAverage`, `SKBarriers_Gaussian_FiberGaussian`, `SKBarriers_Gaussian_GaussianAverage`, `SKBarriers_Gaussian_GaussianResponse`, `SKBarriers_Hierarchy_AverageMeanVariance`, `SKBarriers_Hierarchy_BlockDerivativeSum`, `SKBarriers_Hierarchy_CascadeBlockLaw`, `SKBarriers_Hierarchy_CascadeRebase`, `SKBarriers_Hierarchy_HierarchyBlockTrace`, `SKBarriers_Hierarchy_HierarchyDensity`, `SKBarriers_Hierarchy_HierarchyGaussianLaw`, `SKBarriers_Hierarchy_HierarchyJointLaw`, `SKBarriers_Hierarchy_HierarchyJointMoment`, `SKBarriers_Hierarchy_HierarchyLevels`, `SKBarriers_Hierarchy_HierarchyMomentLevels`, `SKBarriers_Hierarchy_HierarchyPathLaw`, `SKBarriers_Hierarchy_HierarchyPenalty`, `SKBarriers_Hierarchy_HierarchyReplica`, `SKBarriers_Hierarchy_HierarchyReplicaSecond`, `SKBarriers_Hierarchy_HierarchyScoreBound`, `SKBarriers_Hierarchy_RootCalculus`, `SKBarriers_Hierarchy_RootSusceptibility`, `SKBarriers_Hierarchy_RootTranslation`, `SKBarriers_Hierarchy_TimeChainAverageAlgebra`, `SKBarriers_Hierarchy_TimeChainRepresentation`, `SKBarriers_Interpolation_FiniteStatePressureCurve`, `SKBarriers_Interpolation_PenaltyGradientBound`, `SKBarriers_Interpolation_SKAdaptiveDerivative`, `SKBarriers_Interpolation_SKHamiltonianDerivative`, `SKBarriers_Locking_NarrowBaseFactor`, `SKBarriers_Locking_NarrowCDFTrial`, `SKBarriers_Locking_NarrowMomentBound`, `SKBarriers_Locking_SignedLocking`, `SKBarriers_Parisi_CDFAtomicRepresentation`, `SKBarriers_Parisi_CDFChainAverage`, `SKBarriers_Parisi_CDFEndpoint`, `SKBarriers_Parisi_CDFJointSusceptibility`, `SKBarriers_Parisi_CDFOverlap`, `SKBarriers_Parisi_CDFOverlapConvergence`, `SKBarriers_Parisi_CDFPartitionRepresentation`, `SKBarriers_Parisi_CDFPotential`, `SKBarriers_Parisi_CDFSpinRegularity`, `SKBarriers_Parisi_CDFSquareSusceptibility`, `SKBarriers_Parisi_CDFTerminalStability`, `SKBarriers_Parisi_CDFTiltedStability`, `SKBarriers_Parisi_QuantileOverlapContinuity`, `SKBarriers_Parisi_QuantileScalarOverlap`, `SKBarriers_Parisi_QuantileVariation`, `SKBarriers_Parisi_QuantileWeakIntegral`, `SKBarriers_Replicas_MatrixReplicaBridge`, `SKBarriers_Replicas_MergedBranch`, `SKBarriers_Replicas_OverlapCode`, `SKBarriers_Replicas_PairGibbsGap`, `SKBarriers_Replicas_PairRecursion`, `SKBarriers_Replicas_PairSplit`, `SKBarriers_Replicas_TwoPartitionOverlap`, `SKBarriers_Replicas_VectorBranch`, `SKBarriers_Scalar_CovarianceRegular`, `SKBarriers_Scalar_DyadicCDFStability`, `SKBarriers_Scalar_DyadicSpin`, `SKBarriers_Scalar_EmbeddedSites`, `SKBarriers_Scalar_GeneralCDFStability`, `SKBarriers_Scalar_PartitionOverlapContinuity`, `SKBarriers_Scalar_PathExponentialAverage`, `SKBarriers_Scalar_PrefixAlgebra`, `SKBarriers_Scalar_ScalarAverageCalculus`, `SKBarriers_Scalar_ScalarCDFLimit`, `SKBarriers_Scalar_ScalarEndpoint`, `SKBarriers_Scalar_ScalarHierarchy`, `SKBarriers_Scalar_ScalarHierarchyMass`, `SKBarriers_Scalar_ScalarLevelRepresentation`, `SKBarriers_Scalar_ScalarMomentSquare`, `SKBarriers_Scalar_ScalarOverlapContinuity`, `SKBarriers_Scalar_ScalarResponse`, `SKBarriers_Scalar_ScalarSpinRecursion`, `SKBarriers_Scalar_ScalarSplit`, `SKBarriers_Scalar_ScalarSusceptibility`, `SKBarriers_Scalar_ScalarTiltedExpectation`, `SKBarriers_Scalar_ScalarWeightedVector`, `SKBarriers_Scalar_SuffixPartitionSusceptibility`, `SKBarriers_Scalar_TerminalPathIntegral`, `SKBarriers_Scalar_TerminalPathStability`, `SKBarriers_Scalar_TiltedTerminalLimit`, `SKBarriers_Scalar_VectorAverage`, `SKBarriers_Scalar_VectorHierarchy`, `SKBarriers_Scalar_VectorMultiplier`, `SKBarriers_SpinGlass_FiniteLaw`, `SKBarriers_SpinGlass_SpinHessianFormula`, `SKBarriers_SpinGlass_SpinParameterMoments`, `SKBarriers_SpinGlass_SpinParameterRegular`, `SKBarriers_SpinGlass_SpinSiteTensorization`.
--
--   **Imports.** It imports the published bundle `Def_SKBarriers`; the bundles `OAIQ036S002` and `OAIQ036S003` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ036S006`; the statements `OAI.SK.Analytic.equalBlock_average_trace`, `OAI.SK.Analytic.exists_block_adaptive_path`, `OAI.SK.Analytic.exists_scalarCDFParisi_minimizer_locking_data`, `OAI.SK.Analytic.exists_stationary_quantile_sequence`, `OAI.SK.Analytic.fourBlockQuadratic_tent_le`, `OAI.SK.Analytic.matrixFiniteInterpolation_offset`, `OAI.SK.Analytic.narrowCDFTrialCoefficient_quantitative`, `OAI.SK.Analytic.narrowConstrainedPressure_scaled_gap`, `OAI.SK.Analytic.narrowConstrainedPressure_schedule`, `OAI.SK.Analytic.narrowSchedule_value_expansion`, `OAI.SK.Analytic.pairMismatch_pressure_gap`, `OAI.SK.Analytic.quenchedPressure_quantitative_finiteInf`, `OAI.SK.Analytic.quenchedPressure_tendsto_finiteParisiInf`, `OAI.SK.Analytic.scalarCDFJointSusceptibility_quantile_loss`, `OAI.SK.Analytic.scalarCDFParisi_origin_stability`, `OAI.SK.Analytic.scalarCDFPotential_minimum_bound`, `OAI.SK.Analytic.sharedFieldEnergy_variance`, `OAI.SK.Analytic.skBlockPressure_hasDerivAt` and `OAI.SK.Analytic.tripleConstrainedPressure_schedule`; the proofs of `OAI.SK.Analytic.coverage_energy_tail`, `OAI.SK.Analytic.equalBlock_average_trace`, `OAI.SK.Analytic.exists_block_adaptive_path`, `OAI.SK.Analytic.exists_scalarCDFParisi_minimizer_locking_data`, `OAI.SK.Analytic.exists_stationary_quantile_sequence`, `OAI.SK.Analytic.fourBlockQuadratic_tent_le`, `OAI.SK.Analytic.identity_main_of_static_locking`, `OAI.SK.Analytic.matrixFiniteInterpolation_offset`, `OAI.SK.Analytic.narrowCDFTrialCoefficient_quantitative`, `OAI.SK.Analytic.narrowConstrainedPressure_schedule`, `OAI.SK.Analytic.narrowSchedule_value_expansion`, `OAI.SK.Analytic.scalarCDFParisi_origin_stability`, `OAI.SK.Analytic.scalarCDFPotential_minimum_bound`, `OAI.SK.Analytic.sharedFieldEnergy_variance`, `OAI.SK.Analytic.skBlockPressure_hasDerivAt`, `OAI.SK.Analytic.stretched_uniform_coverage`, `OAI.SK.Analytic.tripleConstrainedPressure_schedule` and `OAI.SK.main`.
-- source:
--   OpenAI, Stretched-exponential barriers for typical SK initial states, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Stretched-exponential-barriers-for-typical-SK-initial-states-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability/SKBarriers at commit adc7f12

import Mathlib
import Definitions.Def_SKBarriers
import Definitions.Def_OAIQ036S002
import Definitions.Def_OAIQ036S003

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_ParameterCalculus
attribute [-instance] _root_.OAI.SK.Analytic.cubeFiniteMeasure _root_.OAI.SK.Analytic.fiberGaussian_isGaussian _root_.OAI.SK.Analytic.fiberGaussian_probability _root_.OAI.SK.Analytic.fiberNeZero _root_.OAI.SK.Analytic.fiberSigmaFinite _root_.OAI.SK.Analytic.parameterBorel _root_.OAI.SK.Analytic.parameterMeasurable _root_.OAI.SK.Analytic.parameterSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic

def parameterDerivative (n : ℕ) (f : ParameterSpace n → ℝ) (z : ParameterSpace n) : ℝ :=
  fderiv ℝ f z (parameterAxis n)

end SK.Analytic

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyPenalty
attribute [-instance] _root_.OAI.SK.Analytic.fiberGaussian_isGaussian _root_.OAI.SK.Analytic.fiberGaussian_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic

theorem hierarchyPathWeight_eq (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (u : ℝ) (z : ParameterSpace n) :
    hierarchyPathWeight n m f z = Real.exp (u*f z-hierarchyPenalty n m u f z) := by
  induction n generalizing u with
  | zero => simp only [hierarchyPathWeight,hierarchyPenalty,sub_self,Real.exp_zero]
  | succ n ih =>
    rw [hierarchyPathWeight, ih (fun i => m i.castSucc) _ (m (Fin.last n)), ← Real.exp_add]
    apply congrArg Real.exp
    simp only [hierarchyPenalty]
    ring

end SK.Analytic

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_FiberGaussian
attribute [-instance] _root_.OAI.SK.Analytic.fiberGaussian_isGaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic

theorem hierarchyPathWeight_pos (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (z : ParameterSpace n) :
    0 < hierarchyPathWeight n m f z := by
  rw [hierarchyPathWeight_eq n m f 1]
  exact Real.exp_pos _

theorem hierarchyPathWeight_continuous (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) :
    Continuous (hierarchyPathWeight n m f) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have hs := hf.gaussianStep (m (Fin.last n))
    exact (Real.continuous_exp.comp (continuous_const.mul
      (hf.1.continuous.sub (hs.1.continuous.comp continuous_fst)))).mul
      ((ih (fun i => m i.castSucc) _ hs).comp continuous_fst)

theorem hierarchyPathWeight_normalized (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (x : ℝ) :
    Integrable (hierarchyPathWeight n m f) (fiberGaussian n x) ∧
      (∫ z, hierarchyPathWeight n m f z ∂fiberGaussian n x) = 1 := by
  induction n with
  | zero =>
    constructor
    · change Integrable (fun _ : ℝ => (1 : ℝ)) (Measure.dirac x)
      exact integrable_const _
    · simp [fiberGaussian,hierarchyPathWeight]
  | succ n ih =>
    have ih' := ih (fun i => m i.castSucc) _ (hf.gaussianStep (m (Fin.last n)))
    let w : ParameterSpace n → ℝ := hierarchyPathWeight n (fun i => m i.castSucc)
      (gaussianStep (m (Fin.last n)) f)
    have hi (z : ParameterSpace n) : Integrable
        (fun y => hierarchyPathWeight (n+1) m f (z,y)) (gaussianReal 0 1) := by
      change Integrable (fun y => Real.exp (m (Fin.last n)*
        (f (z,y)-gaussianStep (m (Fin.last n)) f z))*w z) _
      simp_rw [gaussianTransition_density hf]
      exact ((hf.exp_integrable (m (Fin.last n)) z).div_const _).mul_const _
    have he (z : ParameterSpace n) :
        (∫ y, hierarchyPathWeight (n+1) m f (z,y) ∂gaussianReal 0 1) = w z := by
      change (∫ y, Real.exp (m (Fin.last n)*(f (z,y)-gaussianStep (m (Fin.last n)) f z))*w z
        ∂gaussianReal 0 1) = w z
      rw [integral_mul_const,gaussianTransition_integral_one hf,one_mul]
    have hnorm (z : ParameterSpace n) :
        (∫ y, ‖hierarchyPathWeight (n+1) m f (z,y)‖ ∂gaussianReal 0 1) = w z := by
      simp only [Real.norm_eq_abs,abs_of_pos (hierarchyPathWeight_pos _ _ _ _)]
      exact he z
    have hprod : Integrable (hierarchyPathWeight (n+1) m f) (fiberGaussian (n+1) x) := by
      apply (integrable_prod_iff (hierarchyPathWeight_continuous _ _ _ hf).aestronglyMeasurable).2
      refine ⟨ae_of_all _ hi,?_⟩
      simpa only [hnorm] using ih'.1
    refine ⟨hprod,?_⟩
    rw [fiberGaussian,integral_prod _ hprod]
    simp only [he]
    exact ih'.2

def fiberGaussianDensity (n : ℕ) (z : ParameterSpace n) : ℝ :=
  (Real.sqrt (2*Real.pi))⁻¹^n * Real.exp (-coordinateSquare n z/2)

end SK.Analytic

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyJointMoment
attribute [-instance] _root_.OAI.SK.Analytic.fiberGaussian_isGaussian _root_.OAI.SK.Analytic.fiberGaussian_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic

def hierarchyJointMoment {S : Type} [Fintype S] [Nonempty S]
    (n : ℕ) (m : Fin n → ℝ) (U L : S → ParameterSpace n →L[ℝ] ℝ) (a : ℕ) : ℝ :=
  ∑ s, ∫ z, (L s z)^a * Real.exp (-(1/2 : ℝ)*coordinateSquare n z+U s z-
    hierarchyPenalty n m 1 (affineLogPartition (fun _ => 0) U) z) ∂fiberMeasure n 0

end SK.Analytic

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_CoordinateGaussianLaw
attribute [-instance] _root_.OAI.SK.Analytic.fiberGaussian_isGaussian _root_.OAI.SK.disorderPairLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def enumeratedDisorder (N : ℕ) (z : ParameterSpace (Fintype.card (Edge N))) : Disorder N :=
  fun e => coordinateProjection (Fintype.card (Edge N)) ((Fintype.equivFin (Edge N)) e) z

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_ParameterAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

section ParameterAlgebra
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem paramRegular_const (c : ℝ) : ParamRegular (fun _ : P × E => c) := by
  have H := paramSmooth_const (P := P) (E := E) c
  refine ⟨H.1,?_,H.2.2⟩
  intro R
  refine ⟨|c|,abs_nonneg c,?_⟩
  intro p e _
  nlinarith [abs_nonneg c,norm_nonneg e]
end ParameterAlgebra
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_ParameterFiniteLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
section ParameterFiniteLog
variable {P E S : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype S] [Nonempty S]

theorem paramRegular_log_finite_exp (f : S → P × E → ℝ) (hf : ∀ s, ParamRegular (f s)) :
    ParamRegular (fun z => Real.log (∑ s, Real.exp (f s z))) := by
  classical
  let Z := fun z : P × E => ∑ s, Real.exp (f s z)
  have hZ : ParamSmooth Z := ParamSmooth.sum Finset.univ _ (fun s _ => (hf s).expSmooth)
  have hp (z : P × E) : Z z ≠ 0 :=
    (Finset.sum_pos (fun s (_ : s ∈ Finset.univ) => Real.exp_pos (f s z)) Finset.univ_nonempty).ne'
  have hi : ParamExpGrowth (fun z => (Z z)⁻¹) := param_inv_finite_exp_growth f (fun s => (hf s).2.1)
  exact ⟨hZ.1.log hp,param_log_finite_exp_linear f (fun s => (hf s).2.1),
    param_fderiv_log_growth Z id (hZ.1.differentiable (by norm_num)) hp hi hZ.2.2.1,
    param_second_log_growth Z id hZ.1 hp hi hZ.2.2.1 hZ.2.2.2⟩
end ParameterFiniteLog
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
section GaussianAverage
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem gaussianAverage_continuous {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (m : ℝ) {g : E × ℝ → F} (hg : Continuous g) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ z, ‖g z‖ ≤ C) : Continuous (gaussianAverage m f g) := by
  have he := (hf.exp_growths m).1
  have hce : Continuous (fun z => Real.exp (m*f z)) :=
    Real.continuous_exp.comp (continuous_const.mul hf.1.continuous)
  have hweightedGrowth : HasExpGrowth (fun point => Real.exp (m*f point) • g point) :=
    he.congr_bound hC (fun point => by
      rw [norm_smul, mul_comm C]
      exact mul_le_mul_of_nonneg_left (hb point) (norm_nonneg _))
  have hn := hweightedGrowth.continuous_gaussian_integral (hce.smul hg)
  have hd := he.continuous_gaussian_integral hce
  have hp (x : E) : (∫ y, Real.exp (m*f (x,y)) ∂gaussianReal 0 1) ≠ 0 :=
    (integral_exp_pos (hf.exp_integrable m x)).ne'
  have ha : gaussianAverage m f g = fun x =>
      (∫ y, Real.exp (m*f (x,y)) ∂gaussianReal 0 1)⁻¹ •
        ∫ y, Real.exp (m*f (x,y)) • g (x,y) ∂gaussianReal 0 1 := by
    funext x
    exact gaussianStepLaw_integral_inv_smul m f x _
  rw [ha]
  exact (hd.inv₀ hp).smul hn

end GaussianAverage
end SK.Analytic

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianResponse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic

def gaussianResponse (n : ℕ) (F : ParameterSpace n → ℝ) (p x : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (∫ z, fderiv ℝ (fderiv ℝ F) z (coordinateAxis n j) (coordinateAxis n i)
    ∂(fiberGaussian n x).tilted (fun z => p*F z)) +
    p*cov[directionalGradient F (coordinateAxis n i),directionalGradient F (coordinateAxis n j);
      (fiberGaussian n x).tilted (fun z => p*F z)]

end SK.Analytic

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyLevels
attribute [-instance] _root_.OAI.SK.Analytic.fiberGaussian_isGaussian _root_.OAI.SK.Analytic.fiberGaussian_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
attribute [-instance] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyPenalty_sum (n : ℕ) (m : Fin n → ℝ) (u : ℝ)
    (f : ParameterSpace n → ℝ) (z : ParameterSpace n) :
    hierarchyPenalty n m u f z = ∑ j, hierarchyAtom n m u j*hierarchyLevel n m f j z := by
  induction n generalizing u with
  | zero => simp [hierarchyPenalty,hierarchyLevel,hierarchyAtom]
  | succ n ih =>
    rw [hierarchyPenalty,ih (fun i => m i.castSucc) (m (Fin.last n))]
    conv_rhs => rw [Fin.sum_univ_castSucc]
    simp only [hierarchyAtom,hierarchyLevel,Fin.lastCases_last,Fin.lastCases_castSucc]
    ring

end SK.Analytic

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyPathLaw
attribute [-instance] _root_.OAI.SK.Analytic.fiberGaussian_isGaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic

theorem hierarchyPathLaw_probability (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (x : ℝ) :
    IsProbabilityMeasure (hierarchyPathLaw n m f x) := by
  have h := hierarchyPathWeight_normalized n m f hf x
  constructor
  rw [hierarchyPathLaw,withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal h.1 (ae_of_all _ (fun z => (hierarchyPathWeight_pos n m f z).le)),
    h.2,ENNReal.ofReal_one]

theorem hierarchyPathLaw_integral (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (x : ℝ) (g : ParameterSpace n → ℝ) :
    (∫ z, g z ∂hierarchyPathLaw n m f x) =
      ∫ z, hierarchyPathWeight n m f z*g z ∂fiberGaussian n x := by
  rw [hierarchyPathLaw,integral_withDensity_eq_integral_toReal_smul
    (hierarchyPathWeight_continuous n m f hf).measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hierarchyPathWeight_pos _ _ _ _).le,smul_eq_mul]

theorem hierarchyPath_bounded_integrable (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (x : ℝ)
    (g : ParameterSpace n → ℝ) (hg : Continuous g) {C : ℝ} (hb : ∀ z, ‖g z‖ ≤ C) :
    Integrable (fun z => hierarchyPathWeight n m f z*g z) (fiberGaussian n x) := by
  have hw := (hierarchyPathWeight_normalized n m f hf x).1
  apply (hw.mul_const C).mono' ((hierarchyPathWeight_continuous n m f hf).mul hg).aestronglyMeasurable
  filter_upwards [] with z
  change ‖hierarchyPathWeight n m f z*g z‖ ≤ _
  rw [norm_mul,Real.norm_eq_abs,abs_of_pos (hierarchyPathWeight_pos _ _ _ _)]
  exact mul_le_mul_of_nonneg_left (hb z) (hierarchyPathWeight_pos _ _ _ _).le

theorem hierarchyPath_integral_succ (n : ℕ) (m : Fin (n+1) → ℝ)
    (f : ParameterSpace (n+1) → ℝ) (hf : BoundedDerivs f) (x : ℝ)
    (g : ParameterSpace (n+1) → ℝ) (hg : Continuous g) {C : ℝ} (hb : ∀ z, ‖g z‖ ≤ C) :
    (∫ z, g z ∂hierarchyPathLaw (n+1) m f x) =
      ∫ z, gaussianAverage (m (Fin.last n)) f g z
        ∂hierarchyPathLaw n (fun i => m i.castSucc) (gaussianStep (m (Fin.last n)) f) x := by
  rw [hierarchyPathLaw_integral (n+1) m f hf,
    hierarchyPathLaw_integral n _ _ (hf.gaussianStep _),fiberGaussian,
    integral_prod _ (hierarchyPath_bounded_integrable (n+1) m f hf x g hg hb)]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [hierarchyPathWeight]
  have he (y : ℝ) : Real.exp (m (Fin.last n)*(f (z,y)-gaussianStep (m (Fin.last n)) f z)) *
      hierarchyPathWeight n (fun i => m i.castSucc) (gaussianStep (m (Fin.last n)) f) z*g (z,y) =
      hierarchyPathWeight n (fun i => m i.castSucc) (gaussianStep (m (Fin.last n)) f) z *
      (Real.exp (m (Fin.last n)*(f (z,y)-gaussianStep (m (Fin.last n)) f z))*g (z,y)) := by ring
  simp_rw [he]
  rw [integral_const_mul]
  congr 1
  simp_rw [gaussianTransition_density hf]
  rw [gaussianAverage,gaussianStepLaw_integral_inv_smul]
  simp only [smul_eq_mul,div_eq_mul_inv,mul_assoc,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  ring

theorem hierarchyAverage_eq_integral (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (g : ParameterSpace n → ℝ)
    (hg : Continuous g) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ z, ‖g z‖ ≤ C) (x : ℝ) :
    hierarchyAverage n m f g x = ∫ z, g z ∂hierarchyPathLaw n m f x := by
  induction n with
  | zero =>
    rw [hierarchyPathLaw_integral 0 m f hf]
    simp only [hierarchyAverage,hierarchyPathWeight,one_mul,fiberGaussian,integral_dirac]
  | succ n ih =>
    rw [hierarchyPath_integral_succ n m f hf x g hg hb]
    exact ih (fun i => m i.castSucc) _ (hf.gaussianStep _) _
      (gaussianAverage_continuous hf _ hg hC hb) (fun z => gaussianAverage_norm_le hf _ hb z)

end SK.Analytic

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyMomentLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section TranslationMoments
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem gaussianAverage_const_prefix {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (m : ℝ) (g : E → ℝ) : gaussianAverage m f (fun z => g z.1) = g := by
  funext z
  let := gaussianStepLaw_probability hf m z
  simp [gaussianAverage]

end TranslationMoments

theorem hierarchyMomentLevel_bounded_continuous (n : ℕ) (m : Fin n → ℝ)
    (f g : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (hg : Continuous g)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ z, ‖g z‖ ≤ C) (j : Fin (n+1)) :
    Continuous (hierarchyMomentLevel n m f g j) ∧
      ∀ z, ‖hierarchyMomentLevel n m f g j z‖ ≤ C := by
  induction n with
  | zero => exact ⟨hg,hb⟩
  | succ n ih =>
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [hierarchyMomentLevel,Fin.lastCases_last] using And.intro hg hb
    · have H := ih (fun i => m i.castSucc) (gaussianStep (m (Fin.last n)) f)
        (gaussianAverage (m (Fin.last n)) f g) (hf.gaussianStep (m (Fin.last n)))
        (gaussianAverage_continuous hf (m (Fin.last n)) hg hC hb)
        (fun z => gaussianAverage_norm_le hf (m (Fin.last n)) hb z) i
      simp only [hierarchyMomentLevel,Fin.lastCases_castSucc]
      exact ⟨H.1.comp continuous_fst,fun z => H.2 z.1⟩

end SK.Analytic

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_ParameterHierarchyMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section ParameterHierarchyMoment
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem hierarchyMomentLevel_paramSmooth (n : ℕ) (m : Fin n → ℝ)
    (f g : P × ParameterSpace n → ℝ) (hf : ParamRegular f) (hg : ParamSmooth g)
    (j : Fin (n+1)) :
    ParamSmooth (fun z : P × ParameterSpace n =>
      hierarchyMomentLevel n m (fun w => f (z.1,w)) (fun w => g (z.1,w)) j z.2) := by
  induction n with
  | zero => exact hg
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa only [hierarchyMomentLevel,Fin.lastCases_last] using hg
    · have H := ih (fun i => m i.castSucc)
        (gaussianStep (m (Fin.last n)) (fun z : (P × ParameterSpace n) × ℝ => f (z.1.1,(z.1.2,z.2))))
        (gaussianAverage (m (Fin.last n)) (fun z : (P × ParameterSpace n) × ℝ => f (z.1.1,(z.1.2,z.2)))
          (fun z : (P × ParameterSpace n) × ℝ => g (z.1.1,(z.1.2,z.2))))
        (hf.gaussianStep _) (hg.gaussianAverage hf _) j
      simp only [hierarchyMomentLevel,Fin.lastCases_castSucc]
      convert H.fieldComp (ContinuousLinearMap.fst ℝ (ParameterSpace n) ℝ) using 1
      all_goals try with_reducible_and_instances rfl
      rfl
theorem hierarchyAverage_paramSmooth (n : ℕ) (m : Fin n → ℝ)
    (f g : P × ParameterSpace n → ℝ) (hf : ParamRegular f) (hg : ParamSmooth g) :
    ParamSmooth (fun z : P × ℝ =>
      hierarchyAverage n m (fun w => f (z.1,w)) (fun w => g (z.1,w)) z.2) := by
  induction n with
  | zero => exact hg
  | succ n ih =>
    exact ih (fun i => m i.castSucc)
      (gaussianStep (m (Fin.last n)) (fun z : (P × ParameterSpace n) × ℝ => f (z.1.1,(z.1.2,z.2))))
      (gaussianAverage (m (Fin.last n)) (fun z : (P × ParameterSpace n) × ℝ => f (z.1.1,(z.1.2,z.2)))
        (fun z : (P × ParameterSpace n) × ℝ => g (z.1.1,(z.1.2,z.2))))
      (hf.gaussianStep _) (hg.gaussianAverage hf _)

end ParameterHierarchyMoment

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_CascadeBlockLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 1900] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section Translate
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def parameterEmbed : (b : ℕ) → E → ParameterSpace b → CascadeSpace E b
  | 0,x,_ => x
  | b+1,x,z => (parameterEmbed b x z.1,z.2)

def parameterNoise : (b : ℕ) → ParameterSpace b →L[ℝ] CascadeSpace E b
  | 0 => 0
  | b+1 => (parameterNoise b).prodMap (ContinuousLinearMap.id ℝ ℝ)

end Translate
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyJointLaw
attribute [-instance] _root_.OAI.SK.Analytic.fiberGaussian_isGaussian _root_.OAI.SK.Analytic.fiberGaussian_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic

def hierarchyLogDensity {S : Type} [Fintype S] [Nonempty S]
    (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (s : S) (z : ParameterSpace n) : ℝ :=
  -(1/2 : ℝ)*coordinateSquare n z+U s z-
    hierarchyPenalty n m 1 (affineLogPartition (fun _ => 0) U) z

section JointLaw
variable {S : Type} [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]

def hierarchyLaw (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) :
    Measure (S × ParameterSpace n) :=
  ((Measure.count : Measure S).prod (fiberMeasure n 0)).tilted
    (fun sz => hierarchyLogDensity n m U sz.1 sz.2)

end JointLaw
end SK.Analytic

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyGaussianLaw
attribute [-instance] _root_.OAI.SK.Analytic.fiberGaussian_isGaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic
section LawIdentification
variable {S : Type} [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]

def hierarchyTerminalGibbs (n : ℕ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (s : S) (z : ParameterSpace n) : ℝ :=
  Real.exp (U s z-affineLogPartition (fun _ => 0) U z)

def hierarchyGaussianLaw (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) : Measure (S × ParameterSpace n) :=
  ((Measure.count : Measure S).prod (fiberGaussian n 0)).withDensity
    (fun sz => ENNReal.ofReal (hierarchyPathWeight n m
      (affineLogPartition (fun _ => 0) U) sz.2 * hierarchyTerminalGibbs n U sz.1 sz.2))

end LawIdentification
end SK.Analytic

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section HierarchyDensity
variable {S : Type} [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]

def hierarchyPotential (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (s : S) (z : ParameterSpace n) : ℝ :=
  U s z-hierarchyPenalty n m 1 (affineLogPartition (fun _ => 0) U) z

end HierarchyDensity
end SK.Analytic

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_PrefixAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter

namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyPathLaw_integrable (n : ℕ) (m : Fin n → ℝ)
    (f g : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (hg : Continuous g)
    {C : ℝ} (hb : ∀ z, ‖g z‖ ≤ C) (x : ℝ) :
    Integrable g (hierarchyPathLaw n m f x) := by
  let := hierarchyPathLaw_probability n m f hf x
  exact Integrable.of_bound hg.aestronglyMeasurable C (ae_of_all _ hb)

end SK.Analytic

namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section SpinMeans
variable {S : Type} [Fintype S] [Nonempty S]

theorem hierarchySpinMean_regular (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : S → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ s, ‖c s‖ ≤ C) (j : Fin (n+1)) :
    Continuous (hierarchySpinMean n m U c j) ∧ ∀ z, ‖hierarchySpinMean n m U c j z‖ ≤ C :=
  hierarchyMomentLevel_bounded_continuous n m _ _ (affineLogPartition_boundedDerivs (fun _ => 0) U)
    (affineMoment_continuous (fun _ => 0) U c) hC (affineMoment_norm_le (fun _ => 0) U c hc) j

end SpinMeans
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_BlockStein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section MeanSquare
variable {S : Type} [Fintype S] [Nonempty S]

theorem hierarchyMeanSquare_bounds {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ)
    (hc : ∀ i s, ‖c i s‖ ≤ 1) (j : Fin (n+1)) (z : ParameterSpace n) :
    hierarchyMeanSquare n m U c j z ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨normalizedSquare_nonneg _,normalizedSquare_le_one _ ?_⟩
  intro i
  exact (hierarchySpinMean_regular n m U (c i) (by norm_num) (hc i) j).2 z

end MeanSquare

end SK.Analytic
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section MeanTower
variable {S : Type} [Fintype S] [Nonempty S]

theorem hierarchyMeanSquare_continuous {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ)
    (hc : ∀ i s, ‖c i s‖ ≤ 1) (j : Fin (n+1)) :
    Continuous (hierarchyMeanSquare n m U c j) := by
  apply Continuous.div_const
  apply continuous_finsetSum
  intro i _
  exact ((hierarchySpinMean_regular n m U (c i) (by norm_num) (hc i) j).1).pow 2

end MeanTower
end SK.Analytic
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def retainedFieldDirection (D N k : ℕ) (Δ : Fin (k+1) → ℝ) (b : Fin (k+1)) (i : Fin N) :=
  (Real.sqrt (Δ b))⁻¹ • coordinateAxis (blockDimension D N k) (fieldIndex D N k b i)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_AverageMeanVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def sharedFieldEnergy (D N k : ℕ) (Δ : Fin (k+1) → ℝ) (j : Fin k) :=
  blockFieldEnergy (D := D) (N := N) (sharedBlockWeights k Δ j)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_CascadeRebase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 1900] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section CascadeMap
variable {E F : Type}

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {S : Type} [Fintype S]

def rebaseConstants (n : ℕ) (c : S → ℝ) (L : S → CascadeSpace F n →L[ℝ] ℝ) (u : F) : S → ℝ :=
  fun s => c s+L s (cascadeLift n u)

def rebaseLinears (n : ℕ) (L : S → CascadeSpace F n →L[ℝ] ℝ) (A : E →L[ℝ] F) :
    S → CascadeSpace E n →L[ℝ] ℝ := fun s => (L s).comp (cascadeMapCLM n A)

end CascadeMap
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyBlockTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 1900] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section HierarchyBlockTrace
variable {S : Type} [Fintype S] [Nonempty S]

def hierarchySpinWeight (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (j : Fin (n+1)) (z : ParameterSpace n) (s : S) : ℝ :=
  hierarchyMomentLevel n m (affineLogPartition (fun _ => 0) U)
    (fun z => affineGibbs (fun _ => 0) U z s) j z

end HierarchyBlockTrace
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_ExponentialAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
section ExponentialAverage
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem gaussianAverage_exp_representation {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (m : ℝ) (g : E × ℝ → F) (x : E) :
    gaussianAverage m f g x = Real.exp (-m*gaussianStep m f x) •
      ∫ y, Real.exp (m*f (x,y)) • g (x,y) ∂gaussianReal 0 1 := by
  rw [gaussianAverage,gaussianStepLaw_integral hf,← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [smul_smul,← Real.exp_add]
  congr 2
  ring

theorem gaussianAverage_expGrowth {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (m : ℝ) {g : E × ℝ → F} (hg : HasExpGrowth g) :
    HasExpGrowth (gaussianAverage m f g) := by
  have hn := (((hf.exp_growths m).1).smul hg).gaussian_integral
  have hi := ((hf.gaussianStep m).exp_growths (-m)).1
  rw [funext (gaussianAverage_exp_representation hf m g)]
  exact hi.smul hn

theorem gaussianAverage_continuous_of_expGrowth {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (m : ℝ) {g : E × ℝ → F} (hg : HasExpGrowth g) (hc : Continuous g) :
    Continuous (gaussianAverage m f g) := by
  have he := (hf.exp_growths m).1
  have hce : Continuous (fun z => Real.exp (m*f z)) :=
    Real.continuous_exp.comp (continuous_const.mul hf.1.continuous)
  have hn := (he.smul hg).continuous_gaussian_integral (hce.smul hc)
  have hi : Continuous (fun x => Real.exp (-m*gaussianStep m f x)) :=
    Real.continuous_exp.comp (continuous_const.mul (hf.gaussianStep m).1.continuous)
  rw [funext (gaussianAverage_exp_representation hf m g)]
  exact hi.smul hn
end ExponentialAverage

attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyPathWeight_expGrowth (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) :
    HasExpGrowth (hierarchyPathWeight n m f) := by
  have hh := hf.add ((hierarchyPenalty_boundedDerivs n m 1 f hf).const_mul (-1))
  have h := (hh.exp_growths 1).1
  rw [funext (hierarchyPathWeight_eq n m f 1)]
  simpa only [one_mul,neg_one_mul,← sub_eq_add_neg] using h

theorem hierarchyPath_exp_integrable (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (x : ℝ)
    (g : ParameterSpace n → ℝ) (hg : Continuous g) (hb : HasExpGrowth g) :
    Integrable (fun z => hierarchyPathWeight n m f z*g z) (fiberGaussian n x) :=
  ((hierarchyPathWeight_expGrowth n m f hf).mul hb).integrable_fiberGaussian n
    ((hierarchyPathWeight_continuous n m f hf).mul hg) x
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_PathExponentialAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
theorem hierarchyPath_integral_succ_exp (n : ℕ) (m : Fin (n+1) → ℝ)
    (f : ParameterSpace (n+1) → ℝ) (hf : BoundedDerivs f) (x : ℝ)
    (g : ParameterSpace (n+1) → ℝ) (hg : Continuous g) (hb : HasExpGrowth g) :
    (∫ z, g z ∂hierarchyPathLaw (n+1) m f x) =
      ∫ z, gaussianAverage (m (Fin.last n)) f g z
        ∂hierarchyPathLaw n (fun i => m i.castSucc) (gaussianStep (m (Fin.last n)) f) x := by
  rw [hierarchyPathLaw_integral (n+1) m f hf,
    hierarchyPathLaw_integral n _ _ (hf.gaussianStep _),fiberGaussian,
    integral_prod _ (hierarchyPath_exp_integrable (n+1) m f hf x g hg hb)]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [hierarchyPathWeight]
  have he (y : ℝ) : Real.exp (m (Fin.last n)*(f (z,y)-gaussianStep (m (Fin.last n)) f z)) *
      hierarchyPathWeight n (fun i => m i.castSucc) (gaussianStep (m (Fin.last n)) f) z*g (z,y) =
      hierarchyPathWeight n (fun i => m i.castSucc) (gaussianStep (m (Fin.last n)) f) z *
      (Real.exp (m (Fin.last n)*(f (z,y)-gaussianStep (m (Fin.last n)) f z))*g (z,y)) := by ring
  simp_rw [he]
  rw [integral_const_mul]
  congr 1
  simp_rw [gaussianTransition_density hf]
  rw [gaussianAverage,gaussianStepLaw_integral_inv_smul]
  simp only [smul_eq_mul,div_eq_mul_inv,mul_assoc,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  ring

theorem hierarchyAverage_eq_integral_exp (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (g : ParameterSpace n → ℝ)
    (hg : Continuous g) (hb : HasExpGrowth g) (x : ℝ) :
    hierarchyAverage n m f g x = ∫ z, g z ∂hierarchyPathLaw n m f x := by
  induction n with
  | zero =>
    rw [hierarchyPathLaw_integral 0 m f hf]
    simp only [hierarchyAverage,hierarchyPathWeight,one_mul,fiberGaussian,integral_dirac]
  | succ n ih =>
    rw [hierarchyPath_integral_succ_exp n m f hf x g hg hb]
    exact ih (fun i => m i.castSucc) _ (hf.gaussianStep _) _
      (gaussianAverage_continuous_of_expGrowth hf _ hb hg) (gaussianAverage_expGrowth hf _ hb)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_SpinParameterRegular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def spinCoefficientBilinear {N : ℕ} (d : ℕ) (I : Fin d → Finset (Fin N)) (s : Config N) :
    (Fin d → ℝ) →L[ℝ] ParameterSpace d →L[ℝ] ℝ :=
  ∑ i : Fin d, (ContinuousLinearMap.proj i).smulRight
    (spinMonomial s (I i) • coordinateProjection d i)

theorem spinCoefficientBilinear_apply {N : ℕ} (d : ℕ) (I : Fin d → Finset (Fin N))
    (s : Config N) (a : Fin d → ℝ) : spinCoefficientBilinear d I s a = spinExponent d a I s := by
  simp only [spinCoefficientBilinear,sum_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply,spinExponent,coordinateLinear,smul_smul]

theorem spinExponent_paramRegular {N : ℕ} (d : ℕ) (I : Fin d → Finset (Fin N)) (s : Config N) :
    ParamRegular (fun z : (Fin d → ℝ) × ParameterSpace d => spinExponent d z.1 I s z.2) := by
  simpa only [spinCoefficientBilinear_apply] using paramRegular_bilinear (spinCoefficientBilinear d I s)

theorem spinTerminal_paramRegular {N : ℕ} (d : ℕ) (I : Fin d → Finset (Fin N)) (c : Config N → ℝ) :
    ParamRegular (fun z : (Fin d → ℝ) × ParameterSpace d =>
      affineLogPartition c (spinExponent d z.1 I) z.2) := by
  exact paramRegular_log_finite_exp (fun s z => c s+spinExponent d z.1 I s z.2)
    (fun s => (paramRegular_const (c s)).add (spinExponent_paramRegular d I s))

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_BlockDerivativeSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyMeanOverlap_eq_mean_integrals {S : Type} [Fintype S] [Nonempty S]
    {N : ℕ} (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (c : Fin N → S → ℝ) (hc : ∀ i s, ‖c i s‖ ≤ 1) (j : Fin (n+1)) :
    hierarchyMeanOverlap n m U c j =
      (∑ i, ∫ z, (hierarchySpinMean n m U (c i) j z)^2
        ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0) / (N:ℝ) := by
  unfold hierarchyMeanOverlap hierarchyMeanSquare normalizedSquare
  rw [integral_div,integral_finsetSum]
  intro i _
  have hr := hierarchySpinMean_regular n m U (c i) (by norm_num : (0:ℝ) ≤ 1) (hc i) j
  apply hierarchyPathLaw_integrable n m _ _ (affineLogPartition_boundedDerivs (fun _ => 0) U)
    (hr.1.pow 2) (C := 1) _ 0
  intro z
  dsimp only [Pi.pow_apply]
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (hr.2 z)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyReplica
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
open Matrix

attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section HierarchyReplica
variable {S : Type} [Fintype S] [Nonempty S]

def hierarchyOverlapError {N : ℕ} (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (v : S → Fin N → ℝ) (j : Fin (n+1)) : ℝ :=
  ∫ z, finiteReplicaMoment (hierarchySpinWeight n m U j z)
    (fun s t => (normalizedDot (v s) (v t)-hierarchyMeanOverlap n m U (fun i s => v s i) j)^2)
    ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0

end HierarchyReplica
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyReplicaSecond
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section SecondMoment
variable {S : Type} [Fintype S] [Nonempty S]

def hierarchyReplicaSecond {N : ℕ} (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (v : S → Fin N → ℝ) (j : Fin (n+1)) : ℝ :=
  ∫ z, finiteReplicaMoment (hierarchySpinWeight n m U j z)
    (fun s t => (normalizedDot (v s) (v t))^2)
    ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0

end SecondMoment
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_SKHamiltonianDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def skBlockRoot (N k : ℕ) (h : ℝ) (v : Fin (k+1) → ℝ) : ℝ :=
  hierarchyPressure (blockDimension (Fintype.card (Edge N)) N k)
    (blockMass (Fintype.card (Edge N)) N k)
    (affineLogPartition (fun _ => 0) (blockExponent (skInteraction N)
      (fun _ => h/Real.sqrt (N:ℝ)) v)) 0

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_CovarianceRegular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
open Matrix

attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section HierarchyTraceRegular
variable {S : Type} [Fintype S] [Nonempty S]

def hierarchyTraceSquare {N : ℕ} (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (v : S → Fin N → ℝ) (j : Fin (n+1)) (z : ParameterSpace n) : ℝ :=
  let C := finiteCovariance (hierarchySpinWeight n m U j z) v
  (C*C).trace

end HierarchyTraceRegular

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_SpinParameterMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem spinGibbs_paramSmooth {N : ℕ} (d : ℕ) (I : Fin d → Finset (Fin N))
    (c : Config N → ℝ) (s : Config N) :
    ParamSmooth (fun z : (Fin d → ℝ) × ParameterSpace d =>
      affineGibbs c (spinExponent d z.1 I) z.2 s) := by
  have h := (((paramRegular_const (c s)).add (spinExponent_paramRegular d I s)).add
    ((spinTerminal_paramRegular d I c).const_mul (-1))).expSmooth
  have he : (fun z : (Fin d → ℝ) × ParameterSpace d =>
      Real.exp ((c s+spinExponent d z.1 I s z.2)+(-1)*affineLogPartition c (spinExponent d z.1 I) z.2)) =
      (fun z : (Fin d → ℝ) × ParameterSpace d => affineGibbs c (spinExponent d z.1 I) z.2 s) := by
    funext z
    rw [neg_one_mul,← sub_eq_add_neg,affineLogPartition,Real.exp_sub,
      Real.exp_log (affinePartition_pos c (spinExponent d z.1 I) z.2)]
    rfl
  rw [he] at h
  exact h

theorem spinMoment_paramSmooth {N : ℕ} (d : ℕ) (I : Fin d → Finset (Fin N))
    (c v : Config N → ℝ) :
    ParamSmooth (fun z : (Fin d → ℝ) × ParameterSpace d =>
      affineMoment c (spinExponent d z.1 I) v z.2) := by
  exact ParamSmooth.sum Finset.univ _ (fun s _ =>
    (spinGibbs_paramSmooth d I c s).mul (paramSmooth_const (v s)))

theorem spinHierarchyMean_paramSmooth {N : ℕ} (d : ℕ) (m : Fin d → ℝ)
    (I : Fin d → Finset (Fin N)) (v : Config N → ℝ) (j : Fin (d+1)) :
    ParamSmooth (fun z : (Fin d → ℝ) × ParameterSpace d =>
      hierarchySpinMean d m (spinExponent d z.1 I) v j z.2) := by
  exact hierarchyMomentLevel_paramSmooth d m _ _
    (spinTerminal_paramRegular d I (fun _ => 0)) (spinMoment_paramSmooth d I (fun _ => 0) v) j

theorem spinHierarchyMeanSquare_paramSmooth {N K : ℕ} (d : ℕ) (m : Fin d → ℝ)
    (I : Fin d → Finset (Fin N)) (v : Fin K → Config N → ℝ) (j : Fin (d+1)) :
    ParamSmooth (fun z : (Fin d → ℝ) × ParameterSpace d =>
      hierarchyMeanSquare d m (spinExponent d z.1 I) v j z.2) := by
  have h := (ParamSmooth.sum Finset.univ (fun i z =>
    hierarchySpinMean d m (spinExponent d z.1 I) (v i) j z.2 *
      hierarchySpinMean d m (spinExponent d z.1 I) (v i) j z.2)
    (fun i _ => (spinHierarchyMean_paramSmooth d m I (v i) j).mul
      (spinHierarchyMean_paramSmooth d m I (v i) j))).const_mul (K : ℝ)⁻¹
  simpa only [hierarchyMeanSquare,normalizedSquare,pow_two,div_eq_mul_inv,mul_comm] using h

theorem spinHierarchyAverageMeanSquare_paramSmooth {N K : ℕ} (d : ℕ) (m : Fin d → ℝ)
    (I : Fin d → Finset (Fin N)) (v : Fin K → Config N → ℝ) (j : Fin (d+1)) :
    ParamSmooth (fun z : (Fin d → ℝ) × ℝ => hierarchyAverage d m
      (affineLogPartition (fun _ => 0) (spinExponent d z.1 I))
      (hierarchyMeanSquare d m (spinExponent d z.1 I) v j) z.2) := by
  exact hierarchyAverage_paramSmooth d m _ _
    (spinTerminal_paramRegular d I (fun _ => 0)) (spinHierarchyMeanSquare_paramSmooth d m I v j)

theorem spinHierarchyMeanOverlap_eq {N K : ℕ} (d : ℕ) (m : Fin d → ℝ)
    (I : Fin d → Finset (Fin N)) (v : Fin K → Config N → ℝ)
    (hv : ∀ i s, ‖v i s‖ ≤ 1) (j : Fin (d+1)) (a : Fin d → ℝ) :
    hierarchyMeanOverlap d m (spinExponent d a I) v j = hierarchyAverage d m
      (affineLogPartition (fun _ => 0) (spinExponent d a I))
      (hierarchyMeanSquare d m (spinExponent d a I) v j) 0 := by
  exact (hierarchyAverage_eq_integral d m _ (affineLogPartition_boundedDerivs _ _) _
    (hierarchyMeanSquare_continuous d m _ v hv j) (C := 1) zero_le_one
    (fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hierarchyMeanSquare_bounds d m _ v hv j z).1]
      exact (hierarchyMeanSquare_bounds d m _ v hv j z).2) 0).symm

theorem spinHierarchyOverlap_contDiff {N K : ℕ} (d : ℕ) (m : Fin d → ℝ)
    (I : Fin d → Finset (Fin N)) (v : Fin K → Config N → ℝ)
    (hv : ∀ i s, ‖v i s‖ ≤ 1) (j : Fin (d+1)) :
    ContDiff ℝ 2 (fun a : Fin d → ℝ =>
      hierarchyMeanOverlap d m (spinExponent d a I) v j) := by
  simp_rw [spinHierarchyMeanOverlap_eq d m I v hv j]
  exact parameter_contDiff_at_field (spinHierarchyAverageMeanSquare_paramSmooth d m I v j).1 (0 : ℝ)
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_SKAdaptiveDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def skAdaptiveExponent (N k : ℕ) (β u : ℝ) (q : Fin (k+1) → ℝ) :=
  blockExponent (skInteraction N) (fun _ => β*Real.sqrt (1-u)/Real.sqrt (N:ℝ))
    (fun b => β*Real.sqrt (cumulativeGapMap k q b))

def skAdaptiveMean (N k : ℕ) (β u : ℝ) (q : Fin (k+1) → ℝ) (j : Fin (k+1)) : ℝ :=
  hierarchyMeanOverlap (blockDimension (Fintype.card (Edge N)) N k)
    (blockMass (Fintype.card (Edge N)) N k) (skAdaptiveExponent N k β u q)
    (fun i s => spin (s i)) (blockLevel (Fintype.card (Edge N)) N k j)

def skAdaptiveError (N k : ℕ) (β u : ℝ) (q : Fin (k+1) → ℝ) (j : Fin (k+1)) : ℝ :=
  hierarchyOverlapError (blockDimension (Fintype.card (Edge N)) N k)
    (blockMass (Fintype.card (Edge N)) N k) (skAdaptiveExponent N k β u q)
    (fun s i => spin (s i)) (blockLevel (Fintype.card (Edge N)) N k j)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarHierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 1900] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyPressure_scalar_linear (n : ℕ) (m v : Fin n → ℝ) (f c : ℝ → ℝ) :
    hierarchyPressure n m (fun z => f (c (parameter n z)+∑ j, v j*coordinateProjection n j z)) =
      fun x => scalarHierarchy n m v f (c x) := by
  induction n generalizing f with
  | zero => simp [hierarchyPressure,scalarHierarchy,parameter]
  | succ n ih =>
    have he : (fun z : ParameterSpace (n+1) =>
        f (c (parameter (n+1) z)+∑ j, v j*coordinateProjection (n+1) j z)) =
        fun z => f ((c (parameter n z.1)+∑ j : Fin n, v j.castSucc*coordinateProjection n j z.1)+
          v (Fin.last n)*z.2) := by
      funext z
      rw [Fin.sum_univ_castSucc]
      simp [coordinateProjection,parameter,add_assoc]
    rw [he,hierarchyPressure]
    change hierarchyPressure n (fun j => m j.castSucc)
      (fun z => scalarStep (m (Fin.last n)) (v (Fin.last n)) f
        (c (parameter n z)+∑ j, v j.castSucc*coordinateProjection n j z)) = _
    rw [ih]
    rfl
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_SpinSiteTensorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def siteField {D N k : ℕ} (v : Fin (k+1) → ℝ) (i : Fin N) :
    ParameterSpace (blockDimension D N k) →L[ℝ] ℝ :=
  ∑ b, v b • coordinateProjection (blockDimension D N k) (fieldIndex D N k b i)

def siteLogPartition {D N k : ℕ} (v : Fin (k+1) → ℝ) (i : Fin N) :
    ParameterSpace (blockDimension D N k) → ℝ :=
  affineLogPartition (fun _ : Bool => 0) (fun b => spin b • siteField (D := D) v i)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarSpinRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 1900] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarHierarchy_spin_eq (n : ℕ) (m v : Fin n → ℝ) :
    scalarHierarchy n m v scalarSpinTerminal =
      hierarchyPressure n m (affineLogPartition (fun _ : Bool => 0)
        (fun b => spin b • scalarSpinField n v)) := by
  rw [← scalarSpinTerminal_affine]
  exact (hierarchyPressure_scalar_linear n m v scalarSpinTerminal id).symm

theorem scalarHierarchy_spin_regular (n : ℕ) (m v : Fin n → ℝ) :
    BoundedDerivs (scalarHierarchy n m v scalarSpinTerminal) := by
  rw [scalarHierarchy_spin_eq]
  exact hierarchyPressure_boundedDerivs n m _ (affineLogPartition_boundedDerivs _ _)

theorem scalarHierarchy_spin_derivative_bounds (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Set.Icc 0 1) (z : ℝ) :
    let f := scalarHierarchy n m v scalarSpinTerminal
    |fderiv ℝ f z 1| ≤ 1 ∧
      0 < fderiv ℝ (fderiv ℝ f) z 1 1 ∧
      fderiv ℝ (fderiv ℝ f) z 1 1 ≤ 1-(fderiv ℝ f z 1)^2 := by
  dsimp only
  have hL : scalarSpinField n v (parameterAxis n) = 1 := by
    simp [scalarSpinField,coordinateLinear_axis]
  have H := hierarchy_spin_curvature n m
    (affineLogPartition (fun _ : Bool => 0) (fun b => spin b • scalarSpinField n v))
    (affineLogPartition_boundedDerivs _ _) hm (fun x => by
      have H := affineLogPartition_bool_curvature (scalarSpinField n v) x (parameterAxis n) hL
      exact ⟨H.1,H.2.le⟩) z
  rw [← scalarHierarchy_spin_eq] at H
  refine ⟨?_,H⟩
  exact (sq_le_one_iff_abs_le_one _).mp (by linarith [H.1])

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def extendedQuantileParisi (k : ℕ) (β : ℝ) (Q : Fin (k+1) → ℝ) : ℝ :=
  scalarHierarchy (k+1) (quantileMass k)
    (fun b => β*Real.sqrt (cumulativeGapMap k Q b)) scalarSpinTerminal 0 +
    (β^2/4)*(1-2*Q (Fin.last k)+∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(Q j)^2)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_ThermodynamicLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

def finiteParisiValues (β : ℝ) : Set ℝ :=
  {p | ∃ k : ℕ, ∃ Q : Fin (k+1) → ℝ, Monotone Q ∧
    (∀ j, Q j ∈ Set.Icc 0 1) ∧ p = extendedQuantileParisi k β Q}

def finiteParisiInf (β : ℝ) : ℝ := sInf (finiteParisiValues β)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_CoverageTrimming
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def energyTrim {n : ℕ} (J : Disorder n) (e : ℝ) (S : Finset (Config n)) : Finset (Config n) :=
  S.filter (fun x => hamiltonian J x ≤ (n:ℝ)*e)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_HeatBathEnergy
attribute [-instance] _root_.OAI.SK.disorderPairLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def interactionSum {n : ℕ} (J : Disorder n) (v : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, coupling J i j*v i*v j

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_FiniteMarkovPath
attribute [-instance] _root_.OAI.SK.disorderPairLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SK.Analytic

def stationaryPathWeight {n : ℕ} (β : ℝ) (J : Disorder n) (m : ℕ) : (Fin (m+1) → Config n) → ℝ :=
  FiniteMarkov.pathWeight (gibbs β J) (heatBath β J) m

theorem stationaryPathWeight_sum {n : ℕ} (hn : 0<n) (β : ℝ) (J : Disorder n) (m : ℕ) :
    ∑ s,stationaryPathWeight β J m s=1 :=
  FiniteMarkov.pathWeight_sum _ _ (gibbs_sum β J) (heatBath_sum hn β J) m

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_FiniteLaw
attribute [-instance] _root_.OAI.SK.disorderPairLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical
namespace SK.Analytic

def gibbsFiniteLaw {n : ℕ} (β : ℝ) (J : Disorder n) : FiniteLaw (Config n) :=
  ⟨gibbs β J,(fun x => (gibbs_pos β J x).le),gibbs_sum β J⟩

def pathFiniteLaw {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n) (m : ℕ) :
    FiniteLaw (Fin (m+1) → Config n) :=
  ⟨stationaryPathWeight β J m,
    FiniteMarkov.pathWeight_nonneg _ _ (fun x => (gibbs_pos β J x).le) (heatBath_nonneg β J) m,
    stationaryPathWeight_sum hn β J m⟩

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_FiniteCoverageMixing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical
namespace SK.Analytic

def pairStripSet (n : ℕ) (a₀ a₁ : ℝ) : Finset (ReplicaConfig n 2) :=
  Finset.univ.filter (fun s => a₀≤overlap (s 0) (s 1) ∧ overlap (s 0) (s 1)≤a₁)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_QuantileVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def quantileOverlapMean (k : ℕ) (β : ℝ) (Q : Fin (k+1) → ℝ) (j : Fin (k+1)) : ℝ :=
  hierarchyMeanOverlap (blockDimension (Fintype.card (Edge 1)) 1 k)
    (blockMass (Fintype.card (Edge 1)) 1 k)
    (blockExponent (skInteraction 1) (fun _ => 0)
      (fun b => β*Real.sqrt (cumulativeGapMap k Q b)))
    (fun i s => spin (s i)) (blockLevel (Fintype.card (Edge 1)) 1 k j)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_RootCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem rootGradient_continuous (n : ℕ) {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) :
    Continuous (rootGradient n f) :=
  (hf.1.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem rootShift_value_bound (n : ℕ) {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f)
    (h : RootSpinCurvature n f) (z : ParameterSpace n) (t : ℝ) :
    |f (z+t • parameterAxis n)-f z| ≤ |t| := by
  have hd := rootLine_hasDerivAt n hf z
  have hLip : LipschitzWith 1 (fun a : ℝ => f (z+a • parameterAxis n)) :=
    lipschitzWith_of_nnnorm_deriv_le (fun a => (hd a).differentiableAt) (fun a => by
      rw [(hd a).deriv]
      exact_mod_cast (h.bounds (z+a • parameterAxis n)).1)
  simpa only [Real.norm_eq_abs,NNReal.coe_one,one_mul,zero_smul,add_zero,sub_zero] using hLip.norm_sub_le t 0

theorem rootShift_gradient_bound (n : ℕ) {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f)
    (h : RootSpinCurvature n f) (z : ParameterSpace n) (t : ℝ) :
    |rootGradient n f (z+t • parameterAxis n)-rootGradient n f z| ≤ |t| := by
  have hd := rootGradientLine_hasDerivAt n hf z
  have hLip : LipschitzWith 1 (fun a : ℝ => rootGradient n f (z+a • parameterAxis n)) :=
    lipschitzWith_of_nnnorm_deriv_le (fun a => (hd a).differentiableAt) (fun a => by
      rw [(hd a).deriv]
      exact_mod_cast (h.bounds (z+a • parameterAxis n)).2)
  simpa only [Real.norm_eq_abs,NNReal.coe_one,one_mul,zero_smul,add_zero,sub_zero] using hLip.norm_sub_le t 0

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarHierarchyMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem scalarHierarchy_regular (n : ℕ) (m v : Fin n → ℝ) {f : ℝ → ℝ}
    (hf : BoundedDerivs f) : BoundedDerivs (scalarHierarchy n m v f) := by
  induction n generalizing f with
  | zero => exact hf
  | succ n ih => exact ih _ _ (scalarStep_regular hf _ _)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_RootTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem rootTranslate_regular (n : ℕ) (t : ℝ) {f : ParameterSpace n → ℝ}
    (hf : BoundedDerivs f) : BoundedDerivs (rootTranslate n t f) := hf.translate _

theorem gaussianStep_rootTranslate (n : ℕ) (m t : ℝ) (f : ParameterSpace (n+1) → ℝ) :
    gaussianStep m (rootTranslate (n+1) t f)=rootTranslate n t (gaussianStep m f) := by
  funext z
  have he (y : ℝ) : rootTranslate (n+1) t f (z,y)=f (t • parameterAxis n+z,y) := by
    simp only [rootTranslate,parameterAxis,Prod.smul_mk,smul_zero,Prod.mk_add_mk,zero_add]
  simp only [gaussianStep,positiveGaussianLogStep,rootTranslate,parameterAxis,
    Prod.smul_mk,smul_zero,Prod.mk_add_mk,zero_add]

theorem hierarchyPressure_rootTranslate (n : ℕ) (m : Fin n → ℝ) (t : ℝ)
    (f : ParameterSpace n → ℝ) :
    hierarchyPressure n m (rootTranslate n t f)=rootTranslate 0 t (hierarchyPressure n m f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change hierarchyPressure n (fun i => m i.castSucc)
      (gaussianStep (m (Fin.last n)) (rootTranslate (n+1) t f))=_
    rw [gaussianStep_rootTranslate,ih]
    rfl

theorem hierarchyPenalty_rootTranslate (n : ℕ) (m : Fin n → ℝ) (u t : ℝ)
    (f : ParameterSpace n → ℝ) :
    hierarchyPenalty n m u (rootTranslate n t f)=rootTranslate n t (hierarchyPenalty n m u f) := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    funext z
    change (u-m (Fin.last n))*rootTranslate (n+1) t f z+
      hierarchyPenalty n (fun i => m i.castSucc) (m (Fin.last n))
        (gaussianStep (m (Fin.last n)) (rootTranslate (n+1) t f)) z.1=_
    rw [gaussianStep_rootTranslate,ih]
    rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_TerminalPathStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyLevel_uniform_nonexpansive (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, 0 ≤ m i) {f g : ParameterSpace n → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedDerivs g) {ε : ℝ}
    (hfg : ∀ z, |f z-g z| ≤ ε) (j : Fin (n+1)) (z : ParameterSpace n) :
    |hierarchyLevel n m f j z-hierarchyLevel n m g j z| ≤ ε := by
  induction n with
  | zero => exact hfg z
  | succ n ih =>
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [hierarchyLevel, Fin.lastCases_last]
      exact hfg z
    · simp only [hierarchyLevel, Fin.lastCases_castSucc]
      exact ih (fun i => m i.castSucc) (fun i => hm i.castSucc)
        (hf.gaussianStep _) (hg.gaussianStep _)
        (gaussianStep_uniform_nonexpansive hf hg (hm (Fin.last n)) hfg) i z.1

theorem hierarchyPenalty_uniform_nonexpansive (n : ℕ) (m : Fin n → ℝ)
    {u : ℝ} (hu : 0 ≤ u) (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ u)
    (hmono : Monotone m) {f g : ParameterSpace n → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedDerivs g) {ε : ℝ}
    (hfg : ∀ z, |f z-g z| ≤ ε) (z : ParameterSpace n) :
    |hierarchyPenalty n m u f z-hierarchyPenalty n m u g z| ≤ u*ε := by
  simp only [hierarchyPenalty_sum, ← Finset.sum_sub_distrib, ← mul_sub]
  calc
    _ ≤ ∑ j, |hierarchyAtom n m u j*(hierarchyLevel n m f j z-hierarchyLevel n m g j z)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, hierarchyAtom n m u j*|hierarchyLevel n m f j z-hierarchyLevel n m g j z| := by
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_mul, abs_of_nonneg (hierarchyAtom_nonneg n m hu hm hmu hmono j)]
    _ ≤ ∑ j, hierarchyAtom n m u j*ε := Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_left (hierarchyLevel_uniform_nonexpansive n m hm hf hg hfg j z)
        (hierarchyAtom_nonneg n m hu hm hmu hmono j))
    _ = u*ε := by rw [← Finset.sum_mul, hierarchyAtom_sum]

theorem hierarchyPathWeight_ratio_bound (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (hmono : Monotone m)
    {f g : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g)
    {ε : ℝ} (hfg : ∀ z, |f z-g z| ≤ ε) (z : ParameterSpace n) :
    hierarchyPathWeight n m f z ≤ Real.exp (2*ε)*hierarchyPathWeight n m g z := by
  rw [hierarchyPathWeight_eq n m f 1, hierarchyPathWeight_eq n m g 1, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have H := hierarchyPenalty_uniform_nonexpansive n m zero_le_one (fun i => (hm i).1)
    (fun i => (hm i).2) hmono hf hg hfg z
  have Hf := hfg z
  simp only [one_mul] at *
  linarith [(abs_le.mp H).1,(abs_le.mp Hf).2]

theorem hierarchyPathWeight_abs_sub_bound (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (hmono : Monotone m)
    {f g : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g)
    {ε : ℝ} (hε : 0 ≤ ε) (hfg : ∀ z, |f z-g z| ≤ ε) (z : ParameterSpace n) :
    |hierarchyPathWeight n m f z-hierarchyPathWeight n m g z| ≤
      (Real.exp (2*ε)-1)*(hierarchyPathWeight n m f z+hierarchyPathWeight n m g z) := by
  have H₁ := hierarchyPathWeight_ratio_bound n m hm hmono hf hg hfg z
  have H₂ := hierarchyPathWeight_ratio_bound n m hm hmono hg hf
    (fun z => by simpa only [abs_sub_comm] using hfg z) z
  have hC : 0 ≤ Real.exp (2*ε)-1 := sub_nonneg.mpr (Real.one_le_exp (by positivity))
  have hWf := (hierarchyPathWeight_pos n m f z).le
  have hWg := (hierarchyPathWeight_pos n m g z).le
  apply abs_le.mpr
  constructor
  · nlinarith [mul_nonneg hC hWf]
  · nlinarith [mul_nonneg hC hWg]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_TerminalPathIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyPathWeight_integral_abs_sub (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (hmono : Monotone m)
    {f g : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g)
    {ε : ℝ} (hε : 0 ≤ ε) (hfg : ∀ z, |f z-g z| ≤ ε) (x : ℝ) :
    (∫ z, |hierarchyPathWeight n m f z-hierarchyPathWeight n m g z| ∂fiberGaussian n x) ≤
      2*(Real.exp (2*ε)-1) := by
  have iF := hierarchyPathWeight_normalized n m f hf x
  have iG := hierarchyPathWeight_normalized n m g hg x
  calc
    _ ≤ ∫ z, (Real.exp (2*ε)-1)*(hierarchyPathWeight n m f z+hierarchyPathWeight n m g z)
        ∂fiberGaussian n x := integral_mono (iF.1.sub iG.1).abs
      ((iF.1.add iG.1).const_mul _) (hierarchyPathWeight_abs_sub_bound n m hm hmono hf hg hε hfg)
    _ = _ := by rw [integral_const_mul, integral_add iF.1 iG.1, iF.2, iG.2]; ring

theorem hierarchyPathLaw_observable_stability (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (hmono : Monotone m)
    {f g : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g)
    {ε : ℝ} (hε : 0 ≤ ε) (hfg : ∀ z, |f z-g z| ≤ ε)
    {a b : ParameterSpace n → ℝ} (ha : Continuous a) (hb : Continuous b)
    {C δ : ℝ} (hC : 0 ≤ C) (haC : ∀ z, |a z| ≤ C) (hbC : ∀ z, |b z| ≤ C)
    (hab : ∀ z, |a z-b z| ≤ δ) (x : ℝ) :
    |(∫ z, a z ∂hierarchyPathLaw n m f x)-(∫ z, b z ∂hierarchyPathLaw n m g x)| ≤
      δ+2*C*(Real.exp (2*ε)-1) := by
  have iF := hierarchyPathWeight_normalized n m f hf x
  have iG := hierarchyPathWeight_normalized n m g hg x
  have ia := hierarchyPath_exp_integrable n m f hf x a ha
    (HasExpGrowth.of_bounded hC (fun z => by simpa only [Real.norm_eq_abs] using haC z))
  have ib := hierarchyPath_exp_integrable n m g hg x b hb
    (HasExpGrowth.of_bounded hC (fun z => by simpa only [Real.norm_eq_abs] using hbC z))
  have iD : Integrable (fun z => C*|hierarchyPathWeight n m f z-hierarchyPathWeight n m g z|)
      (fiberGaussian n x) := (iF.1.sub iG.1).abs.const_mul C
  rw [hierarchyPathLaw_integral n m f hf, hierarchyPathLaw_integral n m g hg,
    ← integral_sub ia ib]
  have hpoint (z : ParameterSpace n) :
      |hierarchyPathWeight n m f z*a z-hierarchyPathWeight n m g z*b z| ≤
        hierarchyPathWeight n m f z*δ+C*|hierarchyPathWeight n m f z-hierarchyPathWeight n m g z| := by
    calc
      _ = |hierarchyPathWeight n m f z*(a z-b z)+
        (hierarchyPathWeight n m f z-hierarchyPathWeight n m g z)*b z| := by congr 1; ring
      _ ≤ |hierarchyPathWeight n m f z*(a z-b z)|+
          |(hierarchyPathWeight n m f z-hierarchyPathWeight n m g z)*b z| := abs_add_le _ _
      _ ≤ _ := by
        rw [abs_mul,abs_mul,abs_of_pos (hierarchyPathWeight_pos n m f z)]
        exact add_le_add (mul_le_mul_of_nonneg_left (hab z) (hierarchyPathWeight_pos n m f z).le)
          (by
            simpa only [mul_comm C] using
              mul_le_mul_of_nonneg_left (hbC z)
                (abs_nonneg (hierarchyPathWeight n m f z-hierarchyPathWeight n m g z)))
  calc
    _ ≤ ∫ z, |hierarchyPathWeight n m f z*a z-hierarchyPathWeight n m g z*b z| ∂fiberGaussian n x :=
      abs_integral_le_integral_abs
    _ ≤ ∫ z, hierarchyPathWeight n m f z*δ+
        C*|hierarchyPathWeight n m f z-hierarchyPathWeight n m g z| ∂fiberGaussian n x :=
      integral_mono (ia.sub ib).abs ((iF.1.mul_const δ).add ((iF.1.sub iG.1).abs.const_mul C)) hpoint
    _ = δ+C*(∫ z, |hierarchyPathWeight n m f z-hierarchyPathWeight n m g z| ∂fiberGaussian n x) := by
      rw [integral_add (iF.1.mul_const δ) iD,
        integral_mul_const, integral_const_mul, iF.2, one_mul]
    _ ≤ _ := by
      have H := mul_le_mul_of_nonneg_left (hierarchyPathWeight_integral_abs_sub n m hm hmono hf hg hε hfg x) hC
      nlinarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_PenaltyGradientBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem rootGradient_penalty_bound (n : ℕ) (m : Fin n → ℝ)
    {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1)
    (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ u) (hmono : Monotone m)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (h : RootSpinCurvature n f)
    (z : ParameterSpace n) : |rootGradient n (hierarchyPenalty n m u f) z| ≤ u := by
  induction n generalizing u with
  | zero =>
    rw [rootGradient_penalty_zero m u hf,abs_mul,abs_of_nonneg hu.1]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (h.bounds z).1 hu.1
  | succ n ih =>
    let q := m (Fin.last n)
    have hq : q ∈ Icc (0:ℝ) 1 := ⟨hm _,(hmu _).trans hu.2⟩
    have hb := ih (fun i => m i.castSucc) hq (fun i => hm i.castSucc)
      (fun i => hmono (Fin.le_last _))
      (fun _ _ hij => hmono (Fin.castSucc_le_castSucc_iff.mpr hij))
      (hf.gaussianStep q) (h.gaussianStep hf hq) z.1
    rw [rootGradient_penalty_succ n m u hf]
    calc
      _ ≤ |(u-q)*rootGradient (n+1) f z|+
        |rootGradient n (hierarchyPenalty n (fun i => m i.castSucc) q (gaussianStep q f)) z.1| := abs_add_le _ _
      _ ≤ (u-q)*1+q := add_le_add (by
        rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr (hmu _))]
        exact mul_le_mul_of_nonneg_left (h.bounds z).1 (sub_nonneg.mpr (hmu _))) hb
      _ = u := by ring

theorem rootGradient_penalty_shift_bound (n : ℕ) (m : Fin n → ℝ)
    {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1)
    (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ u) (hmono : Monotone m)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (h : RootSpinCurvature n f)
    (z : ParameterSpace n) (t : ℝ) :
    |rootGradient n (hierarchyPenalty n m u f) (z+t • parameterAxis n)-
      rootGradient n (hierarchyPenalty n m u f) z| ≤ u*|t| := by
  induction n generalizing u with
  | zero =>
    rw [rootGradient_penalty_zero m u hf,rootGradient_penalty_zero m u hf,← mul_sub,
      abs_mul,abs_of_nonneg hu.1]
    exact mul_le_mul_of_nonneg_left (rootShift_gradient_bound 0 hf h z t) hu.1
  | succ n ih =>
    let q := m (Fin.last n)
    have hq : q ∈ Icc (0:ℝ) 1 := ⟨hm _,(hmu _).trans hu.2⟩
    have hb := ih (fun i => m i.castSucc) hq (fun i => hm i.castSucc)
      (fun i => hmono (Fin.le_last _))
      (fun _ _ hij => hmono (Fin.castSucc_le_castSucc_iff.mpr hij))
      (hf.gaussianStep q) (h.gaussianStep hf hq) z.1
    rw [rootGradient_penalty_succ n m u hf,rootGradient_penalty_succ n m u hf]
    change |(u-q)*rootGradient (n+1) f (z+t • parameterAxis (n+1))+
      rootGradient n (hierarchyPenalty n (fun i => m i.castSucc) q (gaussianStep q f))
        (z.1+t • parameterAxis n)-
      ((u-q)*rootGradient (n+1) f z+
      rootGradient n (hierarchyPenalty n (fun i => m i.castSucc) q (gaussianStep q f)) z.1)|≤_
    set a := rootGradient (n+1) f (z+t • parameterAxis (n+1))
    set b := rootGradient (n+1) f z
    set c := rootGradient n (hierarchyPenalty n (fun i => m i.castSucc) q (gaussianStep q f))
      (z.1+t • parameterAxis n)
    set d := rootGradient n (hierarchyPenalty n (fun i => m i.castSucc) q (gaussianStep q f)) z.1
    calc
      _ = |(u-q)*(a-b)+(c-d)| := by congr 1; ring
      _ ≤ |(u-q)*(a-b)|+|c-d| := abs_add_le _ _
      _ ≤ (u-q)*|t|+q*|t| := add_le_add (by
        rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr (hmu _))]
        exact mul_le_mul_of_nonneg_left (rootShift_gradient_bound (n+1) hf h z t)
          (sub_nonneg.mpr (hmu _))) hb
      _ = u*|t| := by ring

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_SpinHessianFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def rootPair (n : ℕ) (m : Fin n → ℝ) (f : ParameterSpace n → ℝ)
    (z : ParameterSpace n) : ℝ :=
  rootGradient n f z*rootGradient n (hierarchyPenalty n m 1 f) z

theorem rootPair_continuous (n : ℕ) (m : Fin n → ℝ) {f : ParameterSpace n → ℝ}
    (hf : BoundedDerivs f) : Continuous (rootPair n m f) :=
  (rootGradient_continuous n hf).mul
    (rootGradient_continuous n (hierarchyPenalty_boundedDerivs n m 1 f hf))

theorem rootPair_bound (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (hmono : Monotone m)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (h : RootSpinCurvature n f)
    (z : ParameterSpace n) : |rootPair n m f z|≤1 := by
  rw [rootPair,abs_mul]
  simpa only [one_mul] using mul_le_mul (h.bounds z).1
    (rootGradient_penalty_bound n m ⟨zero_le_one,le_rfl⟩ (fun i => (hm i).1)
      (fun i => (hm i).2) hmono hf h z) (by positivity) zero_le_one

theorem rootPair_shift_bound (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (hmono : Monotone m)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (h : RootSpinCurvature n f)
    (z : ParameterSpace n) (t : ℝ) :
    |rootPair n m f (z+t • parameterAxis n)-rootPair n m f z|≤2*|t| := by
  let P := rootGradient n (hierarchyPenalty n m 1 f)
  have hP (w) : |P w|≤1 := rootGradient_penalty_bound n m ⟨zero_le_one,le_rfl⟩
    (fun i => (hm i).1) (fun i => (hm i).2) hmono hf h w
  have hdP : |P (z+t • parameterAxis n)-P z|≤|t| := by
    simpa only [one_mul] using rootGradient_penalty_shift_bound n m ⟨zero_le_one,le_rfl⟩
      (fun i => (hm i).1) (fun i => (hm i).2) hmono hf h z t
  change |rootGradient n f (z+t • parameterAxis n)*P (z+t • parameterAxis n)-
    rootGradient n f z*P z|≤_
  calc
    _ = |(rootGradient n f (z+t • parameterAxis n)-rootGradient n f z)*P (z+t • parameterAxis n)+
        rootGradient n f z*(P (z+t • parameterAxis n)-P z)| := by congr 1; ring
    _ ≤ |(rootGradient n f (z+t • parameterAxis n)-rootGradient n f z)*P (z+t • parameterAxis n)|+
        |rootGradient n f z*(P (z+t • parameterAxis n)-P z)| := abs_add_le _ _
    _ ≤ |t| *1+1*|t| := by
      simp only [abs_mul]
      exact add_le_add
        (mul_le_mul (rootShift_gradient_bound n hf h z t) (hP _) (by positivity) (abs_nonneg _))
        (mul_le_mul (h.bounds z).1 hdP (by positivity) zero_le_one)
    _ = _ := by ring

theorem hierarchyPressure_rootHessian_spin_formula (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (hmono : Monotone m)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (h : RootSpinCurvature n f)
    (he : ∀ z, rootHessian n f z=1-(rootGradient n f z)^2) (x : ℝ) :
    rootHessian 0 (hierarchyPressure n m f) x=
      1-∫ z, rootPair n m f z ∂hierarchyPathLaw n m f x := by
  have hc := rootPair_continuous n m hf
  have hb := rootPair_bound n m hm hmono hf h
  have hbR : HasExpGrowth (fun z => 1-rootPair n m f z) := HasExpGrowth.of_bounded (by norm_num : (0:ℝ)≤2)
    (fun z => by
      rw [Real.norm_eq_abs]
      calc |1-rootPair n m f z|≤|1|+|rootPair n m f z| := abs_sub _ _
           _ ≤ 2 := by rw [abs_one]; linarith [hb z])
  have hR : rootResponse n m 1 f=fun z => 1-rootPair n m f z := by
    funext z
    rw [rootResponse,he z,rootPair]
    ring
  have hcR : Continuous (fun z => 1-rootPair n m f z) := continuous_const.sub hc
  rw [hierarchyPressure_rootHessian n m 1 hf,hR,
    hierarchyAverage_eq_integral_exp n m f hf _ hcR hbR]
  have iP := hierarchyPathLaw_integrable n m f (rootPair n m f) hf
    hc (fun z => by simpa only [Real.norm_eq_abs] using hb z) x
  let := hierarchyPathLaw_probability n m f hf x
  rw [integral_sub (integrable_const _) iP,integral_const]
  simp

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_RootSusceptibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem rootPair_translate (n : ℕ) (m : Fin n → ℝ) (t : ℝ)
    (f : ParameterSpace n → ℝ) (z : ParameterSpace n) :
    rootPair n m (rootTranslate n t f) z=rootPair n m f (t • parameterAxis n+z) := by
  rw [rootPair,rootGradient_translate,hierarchyPenalty_rootTranslate,rootGradient_translate]
  rfl

theorem hierarchyPressure_rootHessian_shift_modulus (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (hmono : Monotone m)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (h : RootSpinCurvature n f)
    (he : ∀ z, rootHessian n f z=1-(rootGradient n f z)^2) (x t : ℝ) :
    |rootHessian 0 (hierarchyPressure n m f) (x+t)-
      rootHessian 0 (hierarchyPressure n m f) x|≤2*|t|+2*(Real.exp (2*|t|)-1) := by
  have hfT := rootTranslate_regular n t hf
  have hT := h.translate t
  have heT (z) : rootHessian n (rootTranslate n t f) z=
      1-(rootGradient n (rootTranslate n t f) z)^2 := by
    rw [rootHessian_translate,rootGradient_translate]
    exact he _
  have hfg (z) : |rootTranslate n t f z-f z|≤|t| := by
    simpa only [rootTranslate,add_comm] using rootShift_value_bound n hf h z t
  have hpair (z) : |rootPair n m (rootTranslate n t f) z-rootPair n m f z|≤2*|t| := by
    rw [rootPair_translate]
    simpa only [add_comm] using rootPair_shift_bound n m hm hmono hf h z t
  have HT := hierarchyPressure_rootHessian_spin_formula n m hm hmono hfT hT heT x
  rw [hierarchyPressure_rootTranslate,rootHessian_translate] at HT
  simp only [parameterAxis,smul_eq_mul,mul_one] at HT
  rw [add_comm t x] at HT
  rw [HT,hierarchyPressure_rootHessian_spin_formula n m hm hmono hf h he x]
  have H := hierarchyPathLaw_observable_stability n m hm hmono hfT hf (abs_nonneg t) hfg
    (rootPair_continuous n m hfT) (rootPair_continuous n m hf) zero_le_one
    (rootPair_bound n m hm hmono hfT hT) (rootPair_bound n m hm hmono hf h) hpair x
  simpa only [sub_sub_sub_cancel_left,abs_sub_comm,mul_one] using H

theorem hierarchyPressure_rootHessian_shift_bound (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (hmono : Monotone m)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (h : RootSpinCurvature n f)
    (he : ∀ z, rootHessian n f z=1-(rootGradient n f z)^2) (x t : ℝ) :
    |rootHessian 0 (hierarchyPressure n m f) (x+t)-
      rootHessian 0 (hierarchyPressure n m f) x|≤(susceptibilityLipschitzConstant:ℝ)*|t| := by
  change _≤(2+4*Real.exp 2)*|t|
  by_cases ht : |t|≤1
  · have hE := exp_two_mul_sub_one_bound ⟨abs_nonneg t,ht⟩
    have H := hierarchyPressure_rootHessian_shift_modulus n m hm hmono hf h he x t
    nlinarith
  · have hC := h.hierarchyPressure hf m hm
    have H : |rootHessian 0 (hierarchyPressure n m f) (x+t)-
        rootHessian 0 (hierarchyPressure n m f) x|≤2 :=
      (abs_sub _ _).trans (by linarith [(hC.bounds (x+t)).2,(hC.bounds x).2])
    have ht' : 1 < |t| := lt_of_not_ge ht
    have hE := Real.exp_pos (2:ℝ)
    nlinarith [mul_nonneg hE.le (abs_nonneg t)]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarSusceptibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarSpinRoot_curvature (n : ℕ) (v : Fin n → ℝ) :
    RootSpinCurvature n (affineLogPartition (fun _ : Bool => 0)
      (fun b => spin b • scalarSpinField n v)) := by
  intro z
  have hL : scalarSpinField n v (parameterAxis n)=1 := by
    simp [scalarSpinField,coordinateLinear_axis]
  have H := affineLogPartition_bool_curvature (scalarSpinField n v) z (parameterAxis n) hL
  exact ⟨H.1,H.2.le⟩

theorem scalarSpinRoot_curvature_eq (n : ℕ) (v : Fin n → ℝ) (z : ParameterSpace n) :
    rootHessian n (affineLogPartition (fun _ : Bool => 0)
      (fun b => spin b • scalarSpinField n v)) z =
      1-(rootGradient n (affineLogPartition (fun _ : Bool => 0)
        (fun b => spin b • scalarSpinField n v)) z)^2 := by
  have hL : scalarSpinField n v (parameterAxis n)=1 := by
    simp [scalarSpinField,coordinateLinear_axis]
  exact (affineLogPartition_bool_curvature (scalarSpinField n v) z (parameterAxis n) hL).2

theorem scalarHierarchy_spin_hasDerivAt (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    HasDerivAt (scalarHierarchy n m v scalarSpinTerminal)
      (rootGradient 0 (scalarHierarchy n m v scalarSpinTerminal) x) x := by
  exact (scalarHierarchy_spin_regular n m v).1.differentiable (by norm_num) x |>.hasDerivAt

theorem scalarHierarchy_spin_gradient_hasDerivAt (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    HasDerivAt (rootGradient 0 (scalarHierarchy n m v scalarSpinTerminal))
      (rootHessian 0 (scalarHierarchy n m v scalarSpinTerminal) x) x := by
  simpa only [parameterAxis,smul_eq_mul,mul_one,zero_add] using
    rootGradientLine_hasDerivAt 0 (scalarHierarchy_spin_regular n m v) 0 x

theorem scalarHierarchy_spin_gradient_lipschitz (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) :
    LipschitzWith 1 (rootGradient 0 (scalarHierarchy n m v scalarSpinTerminal)) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun x => (scalarHierarchy_spin_gradient_hasDerivAt n m v x).differentiableAt)
  intro x
  rw [(scalarHierarchy_spin_gradient_hasDerivAt n m v x).deriv]
  have H := scalarHierarchy_spin_derivative_bounds n m v hm x
  have h : |rootHessian 0 (scalarHierarchy n m v scalarSpinTerminal) x|≤1 := by
    change |fderiv ℝ (fderiv ℝ (scalarHierarchy n m v scalarSpinTerminal)) x 1 1|≤1
    rw [abs_of_pos H.2.1]
    linarith [H.2.2,sq_nonneg (fderiv ℝ (scalarHierarchy n m v scalarSpinTerminal) x 1)]
  exact_mod_cast h

theorem scalarHierarchy_spin_hessian_lipschitz (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (hmono : Monotone m) :
    LipschitzWith susceptibilityLipschitzConstant
      (rootHessian 0 (scalarHierarchy n m v scalarSpinTerminal)) := by
  rw [scalarHierarchy_spin_eq]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have H := hierarchyPressure_rootHessian_shift_bound n m hm hmono
    (affineLogPartition_boundedDerivs _ _) (scalarSpinRoot_curvature n v)
    (scalarSpinRoot_curvature_eq n v) y (x-y)
  simpa only [add_sub_cancel,Real.dist_eq] using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_DyadicSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarTimeChain_spin_hasDerivAt (β : ℝ) (l : List (ℝ × ℝ≥0)) (x : ℝ) :
    HasDerivAt (scalarTimeChain β l scalarSpinTerminal)
      (rootGradient 0 (scalarTimeChain β l scalarSpinTerminal) x) x := by
  rw [scalarTimeChain_eq_hierarchy]
  exact scalarHierarchy_spin_hasDerivAt _ _ _ _

theorem scalarTimeChain_spin_gradient_hasDerivAt (β : ℝ) (l : List (ℝ × ℝ≥0)) (x : ℝ) :
    HasDerivAt (rootGradient 0 (scalarTimeChain β l scalarSpinTerminal))
      (rootHessian 0 (scalarTimeChain β l scalarSpinTerminal) x) x := by
  rw [scalarTimeChain_eq_hierarchy]
  exact scalarHierarchy_spin_gradient_hasDerivAt _ _ _ _

theorem scalarTimeChain_spin_gradient_lipschitz (β : ℝ) (l : List (ℝ × ℝ≥0))
    (hm : ∀ p ∈ l, p.1 ∈ Icc (0:ℝ) 1) :
    LipschitzWith 1 (rootGradient 0 (scalarTimeChain β l scalarSpinTerminal)) := by
  rw [scalarTimeChain_eq_hierarchy]
  exact scalarHierarchy_spin_gradient_lipschitz _ _ _ (fun i => hm _ (List.get_mem _ i))

theorem scalarTimeChain_spin_hessian_lipschitz (β : ℝ) (l : List (ℝ × ℝ≥0))
    (hm : ∀ p ∈ l, p.1 ∈ Icc (0:ℝ) 1) (hmono : l.Pairwise (fun p q => p.1 ≤ q.1)) :
    LipschitzWith susceptibilityLipschitzConstant
      (rootHessian 0 (scalarTimeChain β l scalarSpinTerminal)) := by
  rw [scalarTimeChain_eq_hierarchy]
  exact scalarHierarchy_spin_hessian_lipschitz _ _ _ (fun i => hm _ (List.get_mem _ i))
    (scalarTimeChain_mass_monotone l hmono)

theorem dyadicScalar_spin_bounds (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (n : ℕ) (s : ℝ) (t : ℝ≥0) (x : ℝ) :
    |rootGradient 0 (dyadicScalar β α n s t scalarSpinTerminal) x| ≤ 1 ∧
      0 < rootHessian 0 (dyadicScalar β α n s t scalarSpinTerminal) x ∧
      rootHessian 0 (dyadicScalar β α n s t scalarSpinTerminal) x ≤
        1-(rootGradient 0 (dyadicScalar β α n s t scalarSpinTerminal) x)^2 := by
  unfold dyadicScalar
  rw [scalarTimeChain_eq_hierarchy]
  exact scalarHierarchy_spin_derivative_bounds _ _ _
    (fun i => dyadicIntervals_mass_bounds hα n s t (List.get_mem _ i)) x

theorem dyadicScalar_successive_geometric {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (hLip : LipschitzWith 1 f) (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (n : ℕ) (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |dyadicScalar β α (n+1) s t f x-dyadicScalar β α n s t f x| ≤
      scalarTimeMassConstant β*(1/2:ℝ)^n := by
  have H := dyadicScalar_successive_bound hf hLip β hα hmono n s t ht x
  have hC := scalarTimeMassConstant_nonneg β
  have ht' : (t:ℝ) ≤ 1 := ht
  have ho : α (s+t)-α s ≤ 1 := by linarith [(hα (s+t)).2,(hα s).1]
  apply H.trans
  calc
    _ ≤ scalarTimeMassConstant β*(t:ℝ)/(2:ℝ)^(n+1) :=
      mul_le_of_le_one_right (by positivity) ho
    _ ≤ scalarTimeMassConstant β/(2:ℝ)^(n+1) :=
      div_le_div_of_nonneg_right (mul_le_of_le_one_right hC ht') (by positivity)
    _ = scalarTimeMassConstant β*(1/2:ℝ)^(n+1) := by rw [div_pow,one_pow]; ring
    _ ≤ scalarTimeMassConstant β*(1/2:ℝ)^n := by
      rw [pow_succ]
      nlinarith [mul_nonneg hC (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) n)]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_TiltedTerminalLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarCDFOperator_terminal_hasDerivAt (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    {f G g dg : ℝ → ℝ} (hf : BoundedDerivs f) (hG : BoundedDerivs G)
    (hg : ∀ y, HasDerivAt G (g y) y) (hdg : ∀ y, HasDerivAt g (dg y) y)
    {K B C : ℝ≥0} (hfK : LipschitzWith K f) (hGB : LipschitzWith B G)
    (hB : ∀ y, |g y| ≤ B) (hC : ∀ y, |dg y| ≤ C)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x a : ℝ) :
    HasDerivAt (fun b => scalarCDFOperator β α s t (primitivePerturbation f G b) x)
      (scalarCDFTerminalDerivative β α s t f G x a) a := by
  apply hasDerivAt_of_tendstoUniformly
    (dyadicScalar_terminal_derivative_uniform β hα hmono hf hG hg hdg hfK hGB hB hC s t ht x)
    (Eventually.of_forall (fun n b =>
      (dyadicScalar_primitive_regular β α n s t hf hG x).1.differentiable (by decide) b |>.hasDerivAt))
    (fun b => (dyadicScalar_primitive_uniform β hα hmono hf hG hfK hGB s t ht x).tendsto_at b) a

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarTiltedExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarHierarchyAverage_eq_integral (n : ℕ) (m v : Fin n → ℝ)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) (hg : Continuous g) {B : ℝ}
    (hB : 0 ≤ B) (hb : ∀ y, |g y| ≤ B) (x : ℝ) :
    scalarHierarchyAverage n m v f g x =
      ∫ z, g (x+coordinateLinear n v z) ∂hierarchyPathLaw n m
        (fun z => f (x+coordinateLinear n v z)) 0 := by
  rw [← hierarchyAverage_scalarParameterTerminal n m v (fun _ => f) (fun _ => g) x 0]
  exact hierarchyAverage_eq_integral n m _ ((hf.translate x).compCLM (coordinateLinear n v)) _
    (hg.comp (continuous_const.add (coordinateLinear n v).continuous)) hB
    (fun z => by simpa only [Real.norm_eq_abs,scalarParameterTerminal,Function.comp_apply,Pi.add_apply] using hb (x+coordinateLinear n v z)) 0

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_VectorHierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section Vector
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[simp] theorem vectorStep_zero (m : ℝ) (f : E → ℝ) : vectorStep m 0 f=f := by
  simp only [vectorStep,smul_zero,add_zero]
  exact gaussianStep_prefix f m

end Vector

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_PairRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section Generic
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def vectorStepAverage (m : ℝ) (v : E) (f g : E → ℝ) : E → ℝ :=
  gaussianAverage m (fun z : E × ℝ => f (z.1+z.2 • v)) (fun z => g (z.1+z.2 • v))
end Generic

def pairIndependentStep (m v : ℝ) (f : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  vectorStep m (v,0) (vectorStep m (0,v) f)

def pairIndependentAverage (m v : ℝ) (f g : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  vectorStepAverage m (v,0) (vectorStep m (0,v) f) (vectorStepAverage m (0,v) f g)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_VectorAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section Vector
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def vectorHierarchyAverage : (n : ℕ) → (Fin n → ℝ) → (Fin n → E) →
    (E → ℝ) → (E → ℝ) → E → ℝ
  | 0,_,_,_,g => g
  | n+1,m,v,f,g => vectorHierarchyAverage n (fun i => m i.castSucc) (fun i => v i.castSucc)
      (vectorStep (m (Fin.last n)) (v (Fin.last n)) f)
      (vectorStepAverage (m (Fin.last n)) (v (Fin.last n)) f g)

end Vector

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_MergedBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def scalarIncrementChain : List BranchIncrement → (ℝ → ℝ) → ℝ → ℝ
  | [], f => f
  | p::l, f => scalarStep p.1 p.2 (scalarIncrementChain l f)

def scalarIncrementAverage : List BranchIncrement → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ
  | [], _, g => g
  | p::l, f, g => scalarStepAverage p.1 p.2 (scalarIncrementChain l f) (scalarIncrementAverage l f g)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_VectorBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section Vector
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def vectorIncrementChain : List (ℝ × E) → (E → ℝ) → E → ℝ
  | [], f => f
  | p::l, f => vectorStep p.1 p.2 (vectorIncrementChain l f)

def vectorIncrementAverage : List (ℝ × E) → (E → ℝ) → (E → ℝ) → E → ℝ
  | [], _, g => g
  | p::l, f, g => vectorStepAverage p.1 p.2 (vectorIncrementChain l f)
      (vectorIncrementAverage l f g)

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

def productBranchChain (l : List (ProductIncrement (E:=E) (F:=F))) : (E × F → ℝ) → E × F → ℝ :=
  vectorIncrementChain (l.map (fun p => (productMass p,productVector p)))

def productBranchAverage (l : List (ProductIncrement (E:=E) (F:=F))) :
    (E × F → ℝ) → (E × F → ℝ) → E × F → ℝ :=
  vectorIncrementAverage (l.map (fun p => (productMass p,productVector p)))

end Vector

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_FiniteStatePressureCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section
variable {S : Type} [Fintype S] [Nonempty S]

def observableExponent (d : ℕ) (O : Fin d → S → ℝ) (a : Fin d → ℝ)
    (s : S) : ParameterSpace d →L[ℝ] ℝ := coordinateLinear d (fun i => a i*O i s)

def observableCoefficientBilinear (d : ℕ) (O : Fin d → S → ℝ) (s : S) :
    (Fin d → ℝ) →L[ℝ] ParameterSpace d →L[ℝ] ℝ :=
  ∑ i : Fin d, (ContinuousLinearMap.proj i).smulRight (O i s • coordinateProjection d i)

end
end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_EmbeddedSites
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section
variable {A : Type} [Fintype A] [Nonempty A]

def embeddedSiteExponent {n r : ℕ} (e : Fin r → Fin n) (V : Fin r → A → ℝ)
    (a : A) : ParameterSpace n →L[ℝ] ℝ := ∑ j, V j a • coordinateProjection n (e j)

end

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyScoreBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section
variable {S : Type} [Fintype S] [Nonempty S]

def hierarchyPathLogDensity (n : ℕ) (m : Fin n → ℝ) (f : ParameterSpace n → ℝ) : ParameterSpace n → ℝ :=
  fun z => f z-hierarchyPenalty n m 1 f z

end

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarCDFLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarSpinTerminal_regular : BoundedDerivs scalarSpinTerminal :=
  scalarHierarchy_spin_regular 0 Fin.elim0 Fin.elim0

theorem dyadicScalar_value_uniform (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    TendstoUniformly (fun n => dyadicScalar β α n s t scalarSpinTerminal)
      (scalarCDFValue β α s t) atTop :=
  (geometric_uniform_limit (fun k => dyadicScalar β α k s t scalarSpinTerminal) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)<1)
    (fun n x => dyadicScalar_successive_geometric scalarSpinTerminal_regular
      scalarSpinTerminal_lipschitz β hα hmono n s t ht x)).1

theorem dyadicScalar_gradient_uniform (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    TendstoUniformly (fun n => rootGradient 0 (dyadicScalar β α n s t scalarSpinTerminal))
      (scalarCDFGradient β α s t) atTop := by
  apply uniformCauchySeq_limUnder
  apply uniformCauchySeq_derivative 1
    (fun n x => scalarTimeChain_spin_hasDerivAt β (dyadicIntervals α n s t) x)
    (fun n => scalarTimeChain_spin_gradient_lipschitz β (dyadicIntervals α n s t)
      (fun _ hp => dyadicIntervals_mass_bounds hα n s t hp))
  exact (tendstoUniformlyOn_univ.mpr (dyadicScalar_value_uniform β hα hmono s t ht)).uniformCauchySeqOn

theorem dyadicScalar_hessian_uniform (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    TendstoUniformly (fun n => rootHessian 0 (dyadicScalar β α n s t scalarSpinTerminal))
      (scalarCDFHessian β α s t) atTop := by
  apply uniformCauchySeq_limUnder
  apply uniformCauchySeq_derivative susceptibilityLipschitzConstant
    (fun n x => scalarTimeChain_spin_gradient_hasDerivAt β (dyadicIntervals α n s t) x)
    (fun n => scalarTimeChain_spin_hessian_lipschitz β (dyadicIntervals α n s t)
      (fun _ hp => dyadicIntervals_mass_bounds hα n s t hp) (dyadicIntervals_pairwise hmono n s t))
  exact (tendstoUniformlyOn_univ.mpr (dyadicScalar_gradient_uniform β hα hmono s t ht)).uniformCauchySeqOn

theorem scalarCDFValue_hasDerivAt (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    HasDerivAt (scalarCDFValue β α s t) (scalarCDFGradient β α s t x) x :=
  hasDerivAt_of_tendstoUniformly (dyadicScalar_gradient_uniform β hα hmono s t ht)
    (Eventually.of_forall (fun n z => scalarTimeChain_spin_hasDerivAt β (dyadicIntervals α n s t) z))
    (fun z => (dyadicScalar_value_uniform β hα hmono s t ht).tendsto_at z) x

theorem scalarCDFGradient_hasDerivAt (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    HasDerivAt (scalarCDFGradient β α s t) (scalarCDFHessian β α s t x) x :=
  hasDerivAt_of_tendstoUniformly (dyadicScalar_hessian_uniform β hα hmono s t ht)
    (Eventually.of_forall (fun n z => scalarTimeChain_spin_gradient_hasDerivAt β (dyadicIntervals α n s t) z))
    (fun z => (dyadicScalar_gradient_uniform β hα hmono s t ht).tendsto_at z) x

theorem scalarCDF_derivative_bounds (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |scalarCDFGradient β α s t x| ≤ 1 ∧ 0 ≤ scalarCDFHessian β α s t x ∧
      scalarCDFHessian β α s t x ≤ 1-(scalarCDFGradient β α s t x)^2 := by
  have hG := (dyadicScalar_gradient_uniform β hα hmono s t ht).tendsto_at x
  have hH := (dyadicScalar_hessian_uniform β hα hmono s t ht).tendsto_at x
  refine ⟨le_of_tendsto hG.abs (Eventually.of_forall (fun n =>
    (dyadicScalar_spin_bounds β hα n s t x).1)),?_,?_⟩
  · exact ge_of_tendsto hH (Eventually.of_forall (fun n =>
      (dyadicScalar_spin_bounds β hα n s t x).2.1.le))
  · exact le_of_tendsto_of_tendsto hH (tendsto_const_nhds.sub (hG.pow 2))
      (Eventually.of_forall (fun n => (dyadicScalar_spin_bounds β hα n s t x).2.2))

theorem scalarCDFHessian_lipschitz (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    LipschitzWith susceptibilityLipschitzConstant (scalarCDFHessian β α s t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have H (n) := (scalarTimeChain_spin_hessian_lipschitz β (dyadicIntervals α n s t)
    (fun _ hp => dyadicIntervals_mass_bounds hα n s t hp)
    (dyadicIntervals_pairwise hmono n s t)).dist_le_mul x y
  exact le_of_tendsto
    (((dyadicScalar_hessian_uniform β hα hmono s t ht).tendsto_at x).dist
      ((dyadicScalar_hessian_uniform β hα hmono s t ht).tendsto_at y)) (Eventually.of_forall H)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarMomentSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def scalarMomentSquare : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ) →
    (ℝ → ℝ) → (ℝ → ℝ) → Fin (n+1) → ℝ → ℝ
  | 0,_,_,_,g,_ => fun x => (g x)^2
  | n+1,m,v,f,g,j => Fin.lastCases
      (scalarHierarchyAverage (n+1) m v f (fun x => (g x)^2))
      (fun i => scalarMomentSquare n (fun i => m i.castSucc) (fun i => v i.castSucc)
        (scalarStep (m (Fin.last n)) (v (Fin.last n)) f)
        (scalarStepAverage (m (Fin.last n)) (v (Fin.last n)) f g) i) j

theorem scalarParameterTerminal_const_regular (n : ℕ) (v : Fin n → ℝ)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (x : ℝ) :
    BoundedDerivs (scalarParameterTerminal n v (fun _ => f) x) :=
  (hf.translate x).compCLM (coordinateLinear n v)

theorem scalarMomentSquare_eq_hierarchyAverage (n : ℕ) (m v : Fin n → ℝ)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (g : ℝ → ℝ) (j : Fin (n+1)) (x a : ℝ) :
    scalarMomentSquare n m v f g j x =
      hierarchyAverage n m (scalarParameterTerminal n v (fun _ => f) x)
        (fun z => (hierarchyMomentLevel n m (scalarParameterTerminal n v (fun _ => f) x)
          (scalarParameterTerminal n v (fun _ => g) x) j z)^2) a := by
  induction n generalizing f g with
  | zero => simp [scalarMomentSquare,hierarchyAverage,hierarchyMomentLevel,
      scalarParameterTerminal,coordinateLinear]
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [scalarMomentSquare,Fin.lastCases_last,hierarchyMomentLevel]
      exact (hierarchyAverage_scalarParameterTerminal (n+1) m v (fun _ => f)
        (fun _ x => (g x)^2) x a).symm
    · simp only [scalarMomentSquare,hierarchyMomentLevel,Fin.lastCases_castSucc,hierarchyAverage]
      rw [gaussianAverage_const_prefix (scalarParameterTerminal_const_regular (n+1) v hf x)
        (m (Fin.last n)) (fun z => (hierarchyMomentLevel n (fun i => m i.castSucc)
          (gaussianStep (m (Fin.last n)) (scalarParameterTerminal (n+1) v (fun _ => f) x))
          (gaussianAverage (m (Fin.last n)) (scalarParameterTerminal (n+1) v (fun _ => f) x)
            (scalarParameterTerminal (n+1) v (fun _ => g) x)) j z)^2)]
      simp only [gaussianStep_scalarParameterTerminal,gaussianAverage_scalarParameterTerminal]
      exact ih (fun i => m i.castSucc) (fun i => v i.castSucc)
        (scalarStep_regular hf _ _) _ j

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarHierarchy_translate (n : ℕ) (m v : Fin n → ℝ) (f : ℝ → ℝ) (c x : ℝ) :
    scalarHierarchy n m v (fun y => f (c+y)) x=scalarHierarchy n m v f (c+x) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [scalarHierarchy]
    rw [funext (scalarStep_translate _ _ c f)]
    exact ih _ _ _

theorem scalarHierarchy_gradient_average (n : ℕ) (m v : Fin n → ℝ)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) (hg : ∀ y, HasDerivAt f (g y) y) (x : ℝ) :
    deriv (scalarHierarchy n m v f) x=scalarHierarchyAverage n m v f g x := by
  have he : (fun a => scalarHierarchy n m v (primitivePerturbation f f a) x)=
      fun a => scalarHierarchy n m v f (x+a) := by
    funext a
    have hp : primitivePerturbation f f a=fun y => f (a+y) := by
      funext y
      simp only [primitivePerturbation,add_sub_cancel_left,add_comm y a]
    rw [hp,scalarHierarchy_translate,add_comm a x]
  have hd := ((scalarHierarchy_regular n m v hf).1.differentiable (by norm_num) x).hasDerivAt
  have hd' : HasDerivAt (scalarHierarchy n m v f) (deriv (scalarHierarchy n m v f) x) (x+0) := by simpa only [add_zero] using hd
  have H := hd'.comp 0 ((hasDerivAt_id (0:ℝ)).const_add x)
  simp only [mul_one] at H
  have H' := scalarHierarchy_primitive_derivative n m v hf hf hg x 0
  have Hd : deriv (fun a => scalarHierarchy n m v f (x+a)) 0=deriv (scalarHierarchy n m v f) x := by
    simpa only [Function.comp_def] using H.deriv
  rw [he,Hd,primitivePerturbation_zero] at H'
  simpa only [add_zero] using H'

theorem scalarMomentSquare_split (a b : ℕ) (m v : Fin (a+b) → ℝ) (f g : ℝ → ℝ) :
    scalarMomentSquare (a+b) m v f g ⟨a, by omega⟩=
      scalarHierarchyAverage a (fun i => m (i.castAdd b)) (fun i => v (i.castAdd b))
        (scalarHierarchy b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) f)
        (fun x => (scalarHierarchyAverage b (fun i => m (i.natAdd a))
          (fun i => v (i.natAdd a)) f g x)^2) := by
  induction b generalizing f g with
  | zero =>
    cases a with
    | zero => rfl
    | succ a =>
      change scalarMomentSquare (a+1) m v f g (Fin.last (a+1))=_
      rw [scalarMomentSquare,Fin.lastCases_last]
      rfl
  | succ b ih =>
    change scalarMomentSquare (a+b+1) m v f g (Fin.castSucc ⟨a, by omega⟩)=_
    rw [scalarMomentSquare,Fin.lastCases_castSucc]
    exact ih (fun i => m i.castSucc) (fun i => v i.castSucc)
      (scalarStep (m (Fin.last (a+b))) (v (Fin.last (a+b))) f)
      (scalarStepAverage (m (Fin.last (a+b))) (v (Fin.last (a+b))) f g)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarResponse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def scalarFiniteResponse (n : ℕ) (m v : Fin n → ℝ) (i : Fin n) (x : ℝ) : ℝ :=
  1-∑ j : Fin (n+1), if i.val < j.val then hierarchyAtom n m 1 j*
    scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j x else 0

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_TimeChainRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFOperator_eq_chain {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α)
    (l : List (ℝ × ℝ≥0)) (hm : ∀ p∈l, p.1 ∈ Icc (0:ℝ) 1)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (hdur : chainDuration l=t)
    (hmodel : TimeChainModels α s l) (x : ℝ) :
    scalarCDFOperator β α s t f x=scalarTimeChain β l f x := by
  have hv := (dyadicScalar_general_uniform hf hLip β hα hmono s t ht).tendsto_at x
  have hz : Tendsto (fun n : ℕ => scalarTimeMassConstantK β K*(t:ℝ)/(2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have H := le_of_tendsto_of_tendsto (hv.sub_const (scalarTimeChain β l f x)).abs
    (hz.mul_const (α (s+t)-α s)) (Eventually.of_forall
      (fun n => dyadicScalar_chain_error hf hLip β hα hmono n l hm s t ht hdur hmodel x))
  simp only [zero_mul] at H
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm H (abs_nonneg _)))

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFChainAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def scalarTimeChainAverage (β : ℝ) (l : List (ℝ × ℝ≥0)) (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  scalarHierarchyAverage l.length (fun i => (l.get i).1)
    (fun i => β*Real.sqrt ((l.get i).2:ℝ)) f g x

theorem scalarCDFAverage_eq_chainAverage {f g dg : ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : ∀ y, HasDerivAt g (dg y) y) (hdg : Continuous dg)
    {K B C : ℝ≥0} (hfK : LipschitzWith K f)
    (hB : ∀ y, |g y| ≤ B) (hC : ∀ y, |dg y| ≤ C)
    (β : ℝ) {α : ℝ → ℝ} (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α)
    (l : List (ℝ × ℝ≥0)) (hm : ∀ p∈l, p.1∈Icc (0:ℝ) 1)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (hdur : chainDuration l=t)
    (hmodel : TimeChainModels α s l) (x : ℝ) :
    scalarCDFAverage β α s t f g x=scalarTimeChainAverage β l f g x := by
  let G := boundedPrimitive g
  have hc : Continuous g := continuous_iff_continuousAt.mpr (fun y => (hg y).continuousAt)
  have hG : BoundedDerivs G := boundedPrimitive_regular hg hdg hB hC
  have hGd : ∀ y, HasDerivAt G (g y) y := boundedPrimitive_hasDerivAt hc
  have hGB : LipschitzWith B G := boundedPrimitive_lipschitz hc hB
  have he : (fun a => scalarCDFOperator β α s t (primitivePerturbation f G a) x)=
      fun a => scalarTimeChain β l (primitivePerturbation f G a) x := by
    funext a
    exact scalarCDFOperator_eq_chain (primitivePerturbation_regular hf hG a)
      (primitivePerturbation_lipschitz hfK hGB a) β hα hmono l hm s t ht hdur hmodel x
  rw [scalarCDFAverage_eq_terminalDerivative β α s t hf hG hGd]
  have hd := (scalarCDFOperator_terminal_hasDerivAt β hα hmono hf hG hGd hg hfK hGB hB hC s t ht x 0).deriv
  rw [he] at hd
  rw [← hd]
  simp only [scalarTimeChain_eq_hierarchy]
  rw [scalarHierarchy_primitive_derivative _ _ _ hf hG hGd,
    primitivePerturbation_zero]
  simp only [add_zero,scalarTimeChainAverage]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFAtomicRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def scalarCDFParisi (β : ℝ) (α : ℝ → ℝ) : ℝ :=
  scalarCDFValue β α 0 1 0-(β^2/2)*∫ s in Icc (0:ℝ) 1, s*α s

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_DyadicCDFStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFValue_cdf_lipschitz (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hαm : Monotone α)
    (hγ : ∀ z, γ z ∈ Icc (0:ℝ) 1) (hγm : Monotone γ)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |scalarCDFValue β α s t x-scalarCDFValue β γ s t x| ≤
      scalarTimeMassConstant β*(∫ z in s..s+t, |α z-γ z|) := by
  have H (n : ℕ) := (dyadicScalar_cdf_mass_bound scalarSpinTerminal_regular
    scalarSpinTerminal_lipschitz β hα hγ n s t ht x).trans
    (mul_le_mul_of_nonneg_left (dyadicCDFDistance_integral_bound hαm hγm n s t)
      (scalarTimeMassConstant_nonneg β))
  have hv := ((dyadicScalar_value_uniform β hα hαm s t ht).tendsto_at x).sub
    ((dyadicScalar_value_uniform β hγ hγm s t ht).tendsto_at x)
  have hzero : Tendsto (fun n : ℕ => (t:ℝ)/(2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hr := (((hzero.mul_const ((α (s+t)-α s)+(γ (s+t)-γ s))).const_add
    (∫ z in s..s+t, |α z-γ z|)).const_mul (scalarTimeMassConstant β))
  have Hlim := le_of_tendsto_of_tendsto hv.abs hr (Eventually.of_forall H)
  simpa only [zero_mul,add_zero] using Hlim

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFSpinRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Topology NNReal
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFValue_lipschitz (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) : LipschitzWith 1 (scalarCDFValue β α s t) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun x => (scalarCDFValue_hasDerivAt β hα hmono s t ht x).differentiableAt)
  intro x
  rw [(scalarCDFValue_hasDerivAt β hα hmono s t ht x).deriv]
  exact_mod_cast (scalarCDF_derivative_bounds β hα hmono s t ht x).1

theorem scalarCDFHessian_abs_le_one (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |scalarCDFHessian β α s t x| ≤ 1 := by
  have H := scalarCDF_derivative_bounds β hα hmono s t ht x
  rw [abs_of_nonneg H.2.1]
  linarith [H.2.2,sq_nonneg (scalarCDFGradient β α s t x)]

theorem scalarCDFGradient_lipschitz (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) : LipschitzWith 1 (scalarCDFGradient β α s t) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun x => (scalarCDFGradient_hasDerivAt β hα hmono s t ht x).differentiableAt)
  intro x
  rw [(scalarCDFGradient_hasDerivAt β hα hmono s t ht x).deriv]
  exact_mod_cast scalarCDFHessian_abs_le_one β hα hmono s t ht x

theorem scalarCDFValue_regular (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) : BoundedDerivs (scalarCDFValue β α s t) :=
  boundedDerivs_of_derivatives (scalarCDFValue_hasDerivAt β hα hmono s t ht)
    (scalarCDFGradient_hasDerivAt β hα hmono s t ht)
    (scalarCDFHessian_lipschitz β hα hmono s t ht).continuous
    (B:=1) (C:=1) (fun x => (scalarCDF_derivative_bounds β hα hmono s t ht x).1)
    (scalarCDFHessian_abs_le_one β hα hmono s t ht)

theorem scalarCDFGradient_cdf_stability (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hαm : Monotone α)
    (hγ : ∀ z, γ z ∈ Icc (0:ℝ) 1) (hγm : Monotone γ)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x h : ℝ) (hh : 0<h) :
    |scalarCDFGradient β α s t x-scalarCDFGradient β γ s t x| ≤
      2*(scalarTimeMassConstant β*(∫ z in s..s+t, |α z-γ z|))/h+2*h := by
  have H := derivative_bound_of_uniform_value_and_lipschitz _ _ (1+1) _
    (fun z => (scalarCDFValue_hasDerivAt β hα hαm s t ht z).sub
      (scalarCDFValue_hasDerivAt β hγ hγm s t ht z))
    ((scalarCDFGradient_lipschitz β hα hαm s t ht).sub
       (scalarCDFGradient_lipschitz β hγ hγm s t ht))
    (scalarCDFValue_cdf_lipschitz β hα hαm hγ hγm s t ht) x h hh
  norm_num only [NNReal.coe_add,NNReal.coe_one,one_add_one_eq_two] at H
  exact H

theorem scalarCDFGradient_sq_regular (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    (∀ x, HasDerivAt (fun y => (scalarCDFGradient β α s t y)^2)
      (2*scalarCDFGradient β α s t x*scalarCDFHessian β α s t x) x) ∧
    Continuous (fun x => 2*scalarCDFGradient β α s t x*scalarCDFHessian β α s t x) ∧
    (∀ x, |(scalarCDFGradient β α s t x)^2| ≤ (1:ℝ)) ∧
    (∀ x, |2*scalarCDFGradient β α s t x*scalarCDFHessian β α s t x| ≤ (2:ℝ)) := by
  refine ⟨?_,continuous_const.mul (scalarCDFGradient_lipschitz β hα hmono s t ht).continuous |>.mul
    (scalarCDFHessian_lipschitz β hα hmono s t ht).continuous,?_,?_⟩
  · intro x
    convert (scalarCDFGradient_hasDerivAt β hα hmono s t ht x).pow 2 using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  · intro x
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (scalarCDF_derivative_bounds β hα hmono s t ht x).1
  · intro x
    calc
      _ = 2*|scalarCDFGradient β α s t x| * |scalarCDFHessian β α s t x| := by simp only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      _ ≤ 2*1*1 := mul_le_mul (mul_le_mul_of_nonneg_left
        (scalarCDF_derivative_bounds β hα hmono s t ht x).1 (by norm_num))
        (scalarCDFHessian_abs_le_one β hα hmono s t ht x) (abs_nonneg _) (by norm_num)
      _ = 2 := by norm_num

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFTerminalStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarHierarchyAverage_terminal_stability (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (hmono : Monotone m)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g)
    {ε : ℝ} (hε : 0 ≤ ε) (hfg : ∀ z, |f z-g z| ≤ ε)
    {a b : ℝ → ℝ} (ha : Continuous a) (hb : Continuous b)
    {C δ : ℝ} (hC : 0 ≤ C) (haC : ∀ z, |a z| ≤ C) (hbC : ∀ z, |b z| ≤ C)
    (hab : ∀ z, |a z-b z| ≤ δ) (x : ℝ) :
    |scalarHierarchyAverage n m v f a x-scalarHierarchyAverage n m v g b x| ≤
      δ+2*C*(Real.exp (2*ε)-1) := by
  rw [scalarHierarchyAverage_eq_integral n m v hf ha hC haC,
    scalarHierarchyAverage_eq_integral n m v hg hb hC hbC]
  exact hierarchyPathLaw_observable_stability n m hm hmono
    ((hf.translate x).compCLM (coordinateLinear n v))
    ((hg.translate x).compCLM (coordinateLinear n v)) hε
    (fun z => hfg (x+coordinateLinear n v z))
    (ha.comp (continuous_const.add (coordinateLinear n v).continuous))
    (hb.comp (continuous_const.add (coordinateLinear n v).continuous))
    hC (fun z => haC (x+coordinateLinear n v z)) (fun z => hbC (x+coordinateLinear n v z))
    (fun z => hab (x+coordinateLinear n v z)) 0

theorem scalarCDFAverage_terminal_stability (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    {f g a b da db : ℝ → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g)
    {K L B C : ℝ≥0} (hfK : LipschitzWith K f) (hgL : LipschitzWith L g)
    (ha : ∀ z, HasDerivAt a (da z) z) (hb : ∀ z, HasDerivAt b (db z) z)
    (hda : Continuous da) (hdb : Continuous db)
    (haB : ∀ z, |a z| ≤ B) (hbB : ∀ z, |b z| ≤ B)
    (hdaC : ∀ z, |da z| ≤ C) (hdbC : ∀ z, |db z| ≤ C)
    {ε δ : ℝ} (hε : 0 ≤ ε) (hfg : ∀ z, |f z-g z| ≤ ε)
    (hab : ∀ z, |a z-b z| ≤ δ) (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |scalarCDFAverage β α s t f a x-scalarCDFAverage β α s t g b x| ≤
      δ+2*(B:ℝ)*(Real.exp (2*ε)-1) := by
  have h₁ := dyadicScalarAverage_tendsto_C1 β hα hmono hf ha hda hfK haB hdaC s t ht x
  have h₂ := dyadicScalarAverage_tendsto_C1 β hα hmono hg hb hdb hgL hbB hdbC s t ht x
  apply le_of_tendsto (h₁.sub h₂).abs
  apply Eventually.of_forall
  intro n
  apply scalarHierarchyAverage_terminal_stability _ _ _
    (fun i => dyadicIntervals_mass_bounds hα n s t (List.get_mem _ _))
    (fun i j hij => ?_)
    hf hg hε hfg
    (continuous_iff_continuousAt.mpr (fun z => (ha z).continuousAt))
    (continuous_iff_continuousAt.mpr (fun z => (hb z).continuousAt))
    B.coe_nonneg haB hbB hab x
  rcases lt_or_eq_of_le hij with hij|rfl
  · exact (List.pairwise_iff_get.mp (dyadicIntervals_pairwise hmono n s t)) i j hij
  · exact le_rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_GeneralCDFStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFOperator_cdf_lipschitz {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hαm : Monotone α)
    (hγ : ∀ z, γ z ∈ Icc (0:ℝ) 1) (hγm : Monotone γ)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |scalarCDFOperator β α s t f x-scalarCDFOperator β γ s t f x| ≤
      scalarTimeMassConstantK β K*(∫ z in s..s+t, |α z-γ z|) := by
  have H (n : ℕ) := (dyadicScalar_cdf_mass_bound_general hf hLip β hα hγ n s t ht x).trans
    (mul_le_mul_of_nonneg_left (dyadicCDFDistance_integral_bound hαm hγm n s t)
      (scalarTimeMassConstantK_nonneg β K))
  have hv := ((dyadicScalar_general_uniform hf hLip β hα hαm s t ht).tendsto_at x).sub
    ((dyadicScalar_general_uniform hf hLip β hγ hγm s t ht).tendsto_at x)
  have hzero : Tendsto (fun n : ℕ => (t:ℝ)/(2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hr := (((hzero.mul_const ((α (s+t)-α s)+(γ (s+t)-γ s))).const_add
    (∫ z in s..s+t, |α z-γ z|)).const_mul (scalarTimeMassConstantK β K))
  have Hlim := le_of_tendsto_of_tendsto hv.abs hr (Eventually.of_forall H)
  simpa only [zero_mul,add_zero] using Hlim

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFTiltedStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Topology NNReal
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFTerminalDerivative_lipschitz (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    {f G g dg : ℝ → ℝ} (hf : BoundedDerivs f) (hG : BoundedDerivs G)
    (hg : ∀ y, HasDerivAt G (g y) y) (hdg : ∀ y, HasDerivAt g (dg y) y)
    {K B C : ℝ≥0} (hfK : LipschitzWith K f) (hGB : LipschitzWith B G)
    (hB : ∀ y, |g y| ≤ B) (hC : ∀ y, |dg y| ≤ C)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    LipschitzWith (C+2*B^2) (scalarCDFTerminalDerivative β α s t f G x) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have H := dyadicScalar_terminal_derivative_uniform β hα hmono hf hG hg hdg hfK hGB hB hC s t ht x
  exact le_of_tendsto ((H.tendsto_at a).dist (H.tendsto_at b)) (Eventually.of_forall
    (fun n => (dyadicScalar_primitive_derivative_lipschitz β hα hmono n s t hf hG hg hdg hB hC x).dist_le_mul a b))

theorem scalarCDFAverage_cdf_stability (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hαm : Monotone α)
    (hγ : ∀ z, γ z ∈ Icc (0:ℝ) 1) (hγm : Monotone γ)
    {f G g dg : ℝ → ℝ} (hf : BoundedDerivs f) (hG : BoundedDerivs G)
    (hg : ∀ y, HasDerivAt G (g y) y) (hdg : ∀ y, HasDerivAt g (dg y) y)
    {K B C : ℝ≥0} (hfK : LipschitzWith K f) (hGB : LipschitzWith B G)
    (hB : ∀ y, |g y| ≤ B) (hC : ∀ y, |dg y| ≤ C)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x h : ℝ) (hh : 0<h) :
    |scalarCDFAverage β α s t f g x-scalarCDFAverage β γ s t f g x| ≤
      2*(scalarTimeMassConstantK β (K+B+B)*(∫ z in s..s+t, |α z-γ z|))/h+
        2*((C:ℝ)+2*(B:ℝ)^2)*h := by
  rw [scalarCDFAverage_eq_terminalDerivative β α s t hf hG hg,
    scalarCDFAverage_eq_terminalDerivative β γ s t hf hG hg]
  have H := derivative_bound_of_uniform_value_and_lipschitz _ _
    ((C+2*B^2)+(C+2*B^2))
    (scalarTimeMassConstantK β (K+B+B)*(∫ z in s..s+t, |α z-γ z|))
    (fun a => (scalarCDFOperator_terminal_hasDerivAt β hα hαm hf hG hg hdg hfK hGB hB hC s t ht x a).sub
      (scalarCDFOperator_terminal_hasDerivAt β hγ hγm hf hG hg hdg hfK hGB hB hC s t ht x a))
    ((scalarCDFTerminalDerivative_lipschitz β hα hαm hf hG hg hdg hfK hGB hB hC s t ht x).sub
      (scalarCDFTerminalDerivative_lipschitz β hγ hγm hf hG hg hdg hfK hGB hB hC s t ht x))
    (fun a => scalarCDFOperator_cdf_lipschitz (primitivePerturbation_regular hf hG a)
      (primitivePerturbation_lipschitz hfK hGB a) β hα hαm hγ hγm s t ht x) 0 h hh
  simpa only [NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_pow,two_mul] using H

theorem scalarCDFAverage_cdf_stability_C1 (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hαm : Monotone α)
    (hγ : ∀ z, γ z ∈ Icc (0:ℝ) 1) (hγm : Monotone γ)
    {f g dg : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : ∀ y, HasDerivAt g (dg y) y) (hdg : Continuous dg)
    {K B C : ℝ≥0} (hfK : LipschitzWith K f)
    (hB : ∀ y, |g y| ≤ B) (hC : ∀ y, |dg y| ≤ C)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x h : ℝ) (hh : 0<h) :
    |scalarCDFAverage β α s t f g x-scalarCDFAverage β γ s t f g x| ≤
      2*(scalarTimeMassConstantK β (K+B+B)*(∫ z in s..s+t, |α z-γ z|))/h+
        2*((C:ℝ)+2*(B:ℝ)^2)*h := by
  have hc : Continuous g := continuous_iff_continuousAt.mpr (fun y => (hg y).continuousAt)
  exact scalarCDFAverage_cdf_stability β hα hαm hγ hγm hf
    (boundedPrimitive_regular hg hdg hB hC) (boundedPrimitive_hasDerivAt hc) hg hfK
    (boundedPrimitive_lipschitz hc hB) hB hC s t ht x h hh

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFOverlap_cdf_stability (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hαm : Monotone α)
    (hγ : ∀ z, γ z ∈ Icc (0:ℝ) 1) (hγm : Monotone γ)
    {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) (h : ℝ) (hh : 0<h) :
    |scalarCDFOverlap β α q-scalarCDFOverlap β γ q| ≤
      (4*scalarTimeMassConstant β+2*scalarTimeMassConstantK β 3)*cdfDistance α γ/h+
        12*h+2*(Real.exp (2*(scalarTimeMassConstant β*cdfDistance α γ))-1) := by
  let t := Real.toNNReal q
  let r := Real.toNNReal (1-q)
  have ht : (t:ℝ)=q := Real.coe_toNNReal q hq.1
  have hr : (r:ℝ)=1-q := Real.coe_toNNReal (1-q) (sub_nonneg.mpr hq.2)
  have ht1 : t ≤ 1 := by rw [← NNReal.coe_le_coe,ht,NNReal.coe_one]; exact hq.2
  have hr1 : r ≤ 1 := by rw [← NNReal.coe_le_coe,hr,NNReal.coe_one]; linarith [hq.1]
  let fα := scalarCDFValue β α q r
  let fγ := scalarCDFValue β γ q r
  let uα := scalarCDFGradient β α q r
  let uγ := scalarCDFGradient β γ q r
  have HA := scalarCDFGradient_sq_regular β hα hαm q r hr1
  have HG := scalarCDFGradient_sq_regular β hγ hγm q r hr1
  have hind : (∫ z in q..q+r, |α z-γ z|) ≤ cdfDistance α γ :=
    cdfDistance_subinterval_le hαm hγm hq.1 (by rw [hr]; linarith)
  have hfg (z : ℝ) : |fα z-fγ z| ≤ scalarTimeMassConstant β*cdfDistance α γ :=
    (scalarCDFValue_cdf_lipschitz β hα hαm hγ hγm q r hr1 z).trans
      (mul_le_mul_of_nonneg_left hind (scalarTimeMassConstant_nonneg β))
  have hug (z : ℝ) : |uα z-uγ z| ≤ 2*(scalarTimeMassConstant β*cdfDistance α γ)/h+2*h :=
    (scalarCDFGradient_cdf_stability β hα hαm hγ hγm q r hr1 z h hh).trans
      (add_le_add (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hind (scalarTimeMassConstant_nonneg β))
          (by norm_num : (0:ℝ) ≤ 2)) hh.le) le_rfl)
  have hsquare (z : ℝ) : |(uα z)^2-(uγ z)^2| ≤
      2*(2*(scalarTimeMassConstant β*cdfDistance α γ)/h+2*h) :=
    (abs_sq_sub_sq_le_two (scalarCDF_derivative_bounds β hα hαm q r hr1 z).1
      (scalarCDF_derivative_bounds β hγ hγm q r hr1 z).1).trans (mul_le_mul_of_nonneg_left (hug z) (by norm_num))
  have H₁ := scalarCDFAverage_terminal_stability β hα hαm
    (scalarCDFValue_regular β hα hαm q r hr1) (scalarCDFValue_regular β hγ hγm q r hr1)
    (scalarCDFValue_lipschitz β hα hαm q r hr1) (scalarCDFValue_lipschitz β hγ hγm q r hr1)
    HA.1 HG.1 HA.2.1 HG.2.1
    (B:=1) (C:=2) HA.2.2.1 HG.2.2.1 HA.2.2.2 HG.2.2.2
    (mul_nonneg (scalarTimeMassConstant_nonneg β) (cdfDistance_nonneg α γ)) hfg hsquare 0 t ht1 0
  have H₂ := scalarCDFAverage_cdf_stability_C1 β hα hαm hγ hγm
    (scalarCDFValue_regular β hγ hγm q r hr1) HG.1 HG.2.1
    (scalarCDFValue_lipschitz β hγ hγm q r hr1) (B:=1) (C:=2) HG.2.2.1 HG.2.2.2 0 t ht1 0 h hh
  have hprefix : (∫ z in (0:ℝ)..0+t, |α z-γ z|) ≤ cdfDistance α γ :=
    cdfDistance_subinterval_le hαm hγm le_rfl (by simpa only [zero_add,ht] using hq.2)
  norm_num only [NNReal.coe_one,NNReal.coe_ofNat,one_pow,one_add_one_eq_two] at H₁ H₂
  have H₂' : |scalarCDFAverage β α 0 t fγ (fun z => (uγ z)^2) 0-
      scalarCDFAverage β γ 0 t fγ (fun z => (uγ z)^2) 0| ≤
      2*(scalarTimeMassConstantK β 3*cdfDistance α γ)/h+8*h := by
    apply H₂.trans
    have H := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hprefix (scalarTimeMassConstantK_nonneg β 3)) (by norm_num : (0:ℝ) ≤ 2)) hh.le
    exact add_le_add H le_rfl
  calc
    _ ≤ |scalarCDFAverage β α 0 t fα (fun z => (uα z)^2) 0-
          scalarCDFAverage β α 0 t fγ (fun z => (uγ z)^2) 0|+
        |scalarCDFAverage β α 0 t fγ (fun z => (uγ z)^2) 0-
          scalarCDFAverage β γ 0 t fγ (fun z => (uγ z)^2) 0| := abs_sub_le _ _ _
    _ ≤ _ := (add_le_add H₁ H₂').trans_eq (by ring)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarAverageCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

@[simp] theorem scalarStep_prefixGradient {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (v : ℝ) (z : ℝ × ℝ) :
    prefixGradient (fun z : ℝ × ℝ => f (z.1+v*z.2)) 1 z=
      rootGradient 0 f (z.1+v*z.2) := by
  have H := ((hf.1.differentiable (by norm_num) (scalarStepLinear v z)).hasFDerivAt.comp z
    (scalarStepLinear v).hasFDerivAt).fderiv
  unfold prefixGradient
  change fderiv ℝ (fun z => f (scalarStepLinear v z)) z (1,0)=_
  simp only [Function.comp_def] at H
  rw [H]
  simp only [ContinuousLinearMap.comp_apply,scalarStepLinear_apply,mul_zero,add_zero]
  rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarWeightedVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def scalarWeightedAverage (n : ℕ) (m v a : Fin n → ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  vectorHierarchyAverage n m (fun i => (v i,a i))
    (fun p : ℝ × ℝ => f p.1) (fun p => p.2^2) (x,0)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowBaseFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def narrowBaseQuadratic (c v w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) : ℝ :=
  let f := scalarIncrementChain t scalarSpinTerminal
  vectorIncrementAverage (narrowRetainedPrefix c v w) (fun p : NarrowRetainedState => f p.1.1+2*f p.2.1)
    (fun p => rootHessian 0 f p.2.1*(p.1.2+p.2.2)^2) 0

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarHierarchyAverage_nonneg_le_one (n : ℕ) (m v : Fin n → ℝ)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) (hg : Continuous g)
    (hb : ∀ y, g y∈Icc (0:ℝ) 1) (x : ℝ) :
    scalarHierarchyAverage n m v f g x∈Icc (0:ℝ) 1 := by
  have hb' : ∀ y, |g y|≤(1:ℝ) := fun y => by rw [abs_of_nonneg (hb y).1]; exact (hb y).2
  rw [scalarHierarchyAverage_eq_integral n m v hf hg zero_le_one hb' x]
  have := hierarchyPathLaw_probability n m _ ((hf.translate x).compCLM (coordinateLinear n v)) 0
  refine ⟨integral_nonneg (fun z => (hb _).1),?_⟩
  have H := norm_integral_le_of_norm_le_const (μ:=hierarchyPathLaw n m
    (fun z => f (x+coordinateLinear n v z)) 0) (C:=1) (f:=fun z => g (x+coordinateLinear n v z))
    (Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hb' (x+coordinateLinear n v z)))
  exact (le_abs_self _).trans (by simpa only [Measure.real,measure_univ,ENNReal.toReal_one,mul_one,Real.norm_eq_abs] using H)

theorem scalarCDFAverage_nonneg_le_one (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α)
    {f g dg : ℝ → ℝ} (hf : BoundedDerivs f) (hg : ∀ y, HasDerivAt g (dg y) y)
    (hdg : Continuous dg) {K C : ℝ≥0} (hfK : LipschitzWith K f)
    (hb : ∀ y, g y∈Icc (0:ℝ) 1) (hC : ∀ y, |dg y|≤C)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (x : ℝ) :
    scalarCDFAverage β α s t f g x∈Icc (0:ℝ) 1 := by
  have hc : Continuous g := continuous_iff_continuousAt.mpr (fun y => (hg y).continuousAt)
  have hB : ∀ y, |g y|≤(1:ℝ≥0) := fun y => by rw [abs_of_nonneg (hb y).1]; exact (hb y).2
  have H := dyadicScalarAverage_tendsto β hα hmono hf (boundedPrimitive_regular hg hdg hB hC)
    (boundedPrimitive_hasDerivAt hc) hg hfK (boundedPrimitive_lipschitz hc hB) hB hC s t ht x
  apply isClosed_Icc.mem_of_tendsto H
  exact Eventually.of_forall (fun n => scalarHierarchyAverage_nonneg_le_one _ _ _ hf hc hb x)

theorem scalarCDFOverlap_nonneg_le_one (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α)
    {q : ℝ} (hq : q∈Icc (0:ℝ) 1) : scalarCDFOverlap β α q∈Icc (0:ℝ) 1 := by
  have ht : Real.toNNReal (1-q)≤1 := by exact_mod_cast Real.toNNReal_le_iff_le_coe.mpr (by simpa using hq.1)
  have hq' : Real.toNNReal q≤1 := Real.toNNReal_le_iff_le_coe.mpr hq.2
  have HR := scalarCDFGradient_sq_regular β hα hmono q (Real.toNNReal (1-q)) ht
  apply scalarCDFAverage_nonneg_le_one β hα hmono
    (scalarCDFValue_regular β hα hmono q (Real.toNNReal (1-q)) ht)
    HR.1 HR.2.1 (scalarCDFValue_lipschitz β hα hmono q (Real.toNNReal (1-q)) ht)
    (fun z => ⟨sq_nonneg _,(le_abs_self ((scalarCDFGradient β α q (Real.toNNReal (1-q)) z)^2)).trans (HR.2.2.1 z)⟩)
    (C:=2) HR.2.2.2 0 (Real.toNNReal q) hq' 0

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_QuantileScalarOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyMeanOverlap_oneSite (n : ℕ) (m v : Fin n → ℝ) (j : Fin (n+1)) :
    hierarchyMeanOverlap n m (fun s : Config 1 => spin (s 0) • coordinateLinear n v)
      (fun i s => spin (s i)) j=scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j 0 := by
  have heF : affineLogPartition (fun _ : Config 1 => 0) (fun s => spin (s 0) • coordinateLinear n v)=
      scalarParameterTerminal n v (fun _ => scalarSpinTerminal) 0 := by
    funext z
    simpa only [scalarParameterTerminal,zero_add] using affineLogPartition_oneConfig (coordinateLinear n v) z
  have heG : affineMoment (fun _ : Config 1 => 0) (fun s => spin (s 0) • coordinateLinear n v) (fun s => spin (s 0))=
      scalarParameterTerminal n v (fun _ => scalarMagnetization) 0 := by
    funext z
    simpa only [scalarParameterTerminal,zero_add] using affineMoment_oneConfig (coordinateLinear n v) z
  rw [hierarchyMeanOverlap_eq_mean_integrals]
  · simp only [Fin.sum_univ_one,Nat.cast_one,div_one,hierarchySpinMean,
      heF,heG]
    let f := scalarParameterTerminal n v (fun _ => scalarSpinTerminal) 0
    have hf : BoundedDerivs f := scalarParameterTerminal_const_regular n v scalarSpinTerminal_regular 0
    have hg := hierarchySpinMean_regular n m
      (fun s : Config 1 => spin (s 0) • coordinateLinear n v) (fun s => spin (s 0))
      (by norm_num : (0:ℝ) ≤ 1) (fun s => by cases s 0 <;> norm_num [spin]) j
    simp only [hierarchySpinMean,heF,heG] at hg
    rw [scalarMomentSquare_eq_hierarchyAverage _ _ _ scalarSpinTerminal_regular _ _ _ 0]
    symm
    apply hierarchyAverage_eq_integral _ _ f hf _ (C:=1)
    · exact (continuous_pow 2).comp hg.1
    · norm_num
    · intro z
      simpa only [f,scalarParameterTerminal,zero_add,norm_pow,one_pow] using
        pow_le_one₀ (norm_nonneg _) (hg.2 z) (n:=2)
  · intro i s
    cases s i <;> norm_num [spin]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFPartitionRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFOperator_eq_partition {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hK : LipschitzWith K f) (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hαm : Monotone α)
    (n : ℕ) (q : Fin (n+1) → ℝ) (hq : Monotone q) (m : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1)
    (hmodel : ∀ i : Fin n, ∀ z ∈ Ico (q i.castSucc) (q i.succ), α z=m i)
    (t : ℝ≥0) (ht : t ≤ 1) (hd : (t:ℝ)=q (Fin.last n)-q 0) (x : ℝ) :
    scalarCDFOperator β α (q 0) t f x=scalarHierarchy n m (timeGridCoefficients n β q) f x := by
  have hdur : chainDuration (partitionTimeChain n q hq m)=t := by
    apply NNReal.coe_injective
    exact (partitionTimeChain_duration n q hq m).trans hd.symm
  have hml (p) (hp : p ∈ partitionTimeChain n q hq m) : p.1 ∈ Icc (0:ℝ) 1 := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    exact hm i
  have H := scalarCDFOperator_eq_chain hf hK β hα hαm (partitionTimeChain n q hq m) hml
    (q 0) t ht hdur (partitionTimeChain_models n q hq m hmodel) x
  simp only [partitionTimeChain,scalarTimeChain_ofFn,NNReal.coe_mk] at H
  exact H

theorem scalarHierarchyAverage_cast {n l : ℕ} (hn : n=l) (m v : Fin l → ℝ)
    (f g : ℝ → ℝ) :
    scalarHierarchyAverage n (fun i => m (Fin.cast hn i)) (fun i => v (Fin.cast hn i)) f g=
      scalarHierarchyAverage l m v f g := by
  subst l
  rfl

theorem scalarTimeChainAverage_ofFn (n : ℕ) (β : ℝ) (p : Fin n → ℝ × ℝ≥0) (f g : ℝ → ℝ) :
    scalarTimeChainAverage β (List.ofFn p) f g=
      scalarHierarchyAverage n (fun i => (p i).1) (fun i => β*Real.sqrt ((p i).2:ℝ)) f g := by
  unfold scalarTimeChainAverage
  simp only [List.get_ofFn]
  exact scalarHierarchyAverage_cast (show (List.ofFn p).length=n from List.length_ofFn)
    (fun i => (p i).1) (fun i => β*Real.sqrt ((p i).2:ℝ)) f g

theorem scalarCDFAverage_eq_partition {f g dg : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : ∀ y, HasDerivAt g (dg y) y) (hdg : Continuous dg)
    {K B C : ℝ≥0} (hK : LipschitzWith K f) (hB : ∀ y, |g y| ≤ B) (hC : ∀ y, |dg y| ≤ C)
    (β : ℝ) {α : ℝ → ℝ} (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hαm : Monotone α)
    (n : ℕ) (q : Fin (n+1) → ℝ) (hq : Monotone q) (m : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1)
    (hmodel : ∀ i : Fin n, ∀ z ∈ Ico (q i.castSucc) (q i.succ), α z=m i)
    (t : ℝ≥0) (ht : t ≤ 1) (hd : (t:ℝ)=q (Fin.last n)-q 0) (x : ℝ) :
    scalarCDFAverage β α (q 0) t f g x=scalarHierarchyAverage n m (timeGridCoefficients n β q) f g x := by
  have hdur : chainDuration (partitionTimeChain n q hq m)=t := by
    apply NNReal.coe_injective
    exact (partitionTimeChain_duration n q hq m).trans hd.symm
  have hml (p) (hp : p ∈ partitionTimeChain n q hq m) : p.1 ∈ Icc (0:ℝ) 1 := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    exact hm i
  have H := scalarCDFAverage_eq_chainAverage hf hg hdg hK hB hC β hα hαm
    (partitionTimeChain n q hq m) hml (q 0) t ht hdur (partitionTimeChain_models n q hq m hmodel) x
  simp only [partitionTimeChain,scalarTimeChainAverage_ofFn,NNReal.coe_mk] at H
  exact H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TwoPartitionOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFOverlap_eq_two_partitions (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (a b : ℕ) (q : Fin (a+1) → ℝ) (p : Fin (b+1) → ℝ)
    (hq : Monotone q) (hp : Monotone p) (hq0 : q 0=0) (hp1 : p (Fin.last b)=1)
    (hr : q (Fin.last a)=p 0) (m : Fin a → ℝ) (l : Fin b → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hl : ∀ i, l i∈Icc (0:ℝ) 1)
    (hmodelq : ∀ i : Fin a, ∀ z∈Ico (q i.castSucc) (q i.succ), α z=m i)
    (hmodelp : ∀ i : Fin b, ∀ z∈Ico (p i.castSucc) (p i.succ), α z=l i) :
    scalarCDFOverlap β α (p 0)=
      scalarMomentSquare (a+b) (Fin.append m l)
        (Fin.append (timeGridCoefficients a β q) (timeGridCoefficients b β p))
        scalarSpinTerminal scalarMagnetization ⟨a,by omega⟩ 0 := by
  let r := p 0
  have hr0 : r∈Icc (0:ℝ) 1 := by
    constructor
    · change 0 ≤ p 0
      rw [← hr,← hq0]; exact hq (Fin.zero_le _)
    · rw [← hp1]; exact hp (Fin.le_last _)
  let t := Real.toNNReal r
  let s := Real.toNNReal (1-r)
  have ht : (t:ℝ)=r := Real.coe_toNNReal r hr0.1
  have hs : (s:ℝ)=1-r := Real.coe_toNNReal (1-r) (sub_nonneg.mpr hr0.2)
  have ht1 : t≤1 := by rw [← NNReal.coe_le_coe,ht,NNReal.coe_one]; exact hr0.2
  have hs1 : s≤1 := by rw [← NNReal.coe_le_coe,hs,NNReal.coe_one]; linarith [hr0.1]
  let f := scalarCDFValue β α r s
  let u := scalarCDFGradient β α r s
  have hsuffix : f=scalarHierarchy b l (timeGridCoefficients b β p) scalarSpinTerminal := by
    funext x
    exact scalarCDFOperator_eq_partition scalarSpinTerminal_regular scalarSpinTerminal_lipschitz
      β hα hαm b p hp l hl hmodelp s hs1 (by rw [hp1]; exact hs) x
  have hu : u=scalarHierarchyAverage b l (timeGridCoefficients b β p)
      scalarSpinTerminal scalarMagnetization := by
    funext x
    have H := (scalarCDFValue_hasDerivAt β hα hαm r s hs1 x).deriv
    change deriv f x=u x at H
    rw [hsuffix,scalarHierarchy_gradient_average _ _ _ scalarSpinTerminal_regular
      scalarSpinTerminal_hasDerivAt] at H
    exact H.symm
  have HG := scalarCDFGradient_sq_regular β hα hαm r s hs1
  have H := scalarCDFAverage_eq_partition (scalarCDFValue_regular β hα hαm r s hs1)
    HG.1 HG.2.1 (scalarCDFValue_lipschitz β hα hαm r s hs1)
    (B:=1) (C:=2) HG.2.2.1 HG.2.2.2 β hα hαm a q hq m hm hmodelq t ht1
    (by rw [hr,hq0,sub_zero]; exact ht) 0
  rw [hq0] at H
  change scalarCDFAverage β α 0 t f (fun z => (u z)^2) 0=_ at H
  change scalarCDFAverage β α 0 t f (fun z => (u z)^2) 0=_
  rw [H,scalarMomentSquare_split]
  simp only [Fin.append_left,Fin.append_right]
  rw [← hsuffix,← hu]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarOverlapContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem spinExponent_oneSite (n : ℕ) (a : Fin n → ℝ) :
    spinExponent n a (fun _ => ({0}:Finset (Fin 1)))=
      fun s : Config 1 => spin (s 0) • coordinateLinear n a := by
  funext s
  ext z
  simp only [spinExponent,spinMonomial,Finset.prod_singleton,coordinateLinear_apply,
    smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem scalarMomentSquare_contDiff_coeff (n : ℕ) (m : Fin n → ℝ) (j : Fin (n+1)) :
    ContDiff ℝ 2 (fun v : Fin n → ℝ =>
      scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j 0) := by
  have H := spinHierarchyOverlap_contDiff n m (fun _ => ({0}:Finset (Fin 1)))
    (fun i s => spin (s i)) (by intro i s; cases s i <;> norm_num [spin]) j
  simpa only [spinExponent_oneSite,hierarchyMeanOverlap_oneSite] using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_PartitionOverlapContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFOverlap_continuousOn_partition (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (n : ℕ) (q : Fin (n+1) → ℝ) (hq : Monotone q)
    (hq0 : q 0=0) (hq1 : q (Fin.last n)=1)
    (m : Fin n → ℝ) (hm : ∀ i, m i∈Icc (0:ℝ) 1)
    (hmodel : ∀ i : Fin n, ∀ z∈Ico (q i.castSucc) (q i.succ), α z=m i) :
    ContinuousOn (scalarCDFOverlap β α) (Icc (0:ℝ) 1) := by
  let v : ℝ → Fin (n+n) → ℝ := fun r =>
    Fin.append (timeGridCoefficients n β (fun i => min (q i) r))
      (timeGridCoefficients n β (fun i => max (q i) r))
  have hc : Continuous v := by
    apply continuous_pi
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp only [v,Fin.append_left,timeGridCoefficients]
      fun_prop
    · intro j
      simp only [v,Fin.append_right,timeGridCoefficients]
      fun_prop
  have H := (scalarMomentSquare_contDiff_coeff (n+n) (Fin.append m m) ⟨n,by omega⟩).continuous.comp hc
  apply H.continuousOn.congr
  intro r hr
  have hpre (i : Fin n) (z : ℝ) (hz : z∈Ico (min (q i.castSucc) r) (min (q i.succ) r)) :
      α z=m i := by
    apply hmodel i z
    constructor
    · rcases min_le_iff.mp hz.1 with h|h
      · exact h
      · exact False.elim (not_lt_of_ge h (lt_min_iff.mp hz.2).2)
    · exact (lt_min_iff.mp hz.2).1
  have hpost (i : Fin n) (z : ℝ) (hz : z∈Ico (max (q i.castSucc) r) (max (q i.succ) r)) :
      α z=m i := by
    apply hmodel i z
    constructor
    · exact (le_max_left _ _).trans hz.1
    · rcases lt_max_iff.mp hz.2 with h|h
      · exact h
      · exact False.elim (not_lt_of_ge ((le_max_right _ _).trans hz.1) h)
  have H' := scalarCDFOverlap_eq_two_partitions β hα hαm n n
    (fun i => min (q i) r) (fun i => max (q i) r)
    (by intro i j hij; exact min_le_min (hq hij) le_rfl)
    (by intro i j hij; exact max_le_max (hq hij) le_rfl)
    (by simp only [hq0,min_eq_left hr.1])
    (by simp only [hq1,max_eq_left hr.2])
    (by simp only [hq1,hq0,min_eq_right hr.2,max_eq_right hr.1])
    m m hm hm hpre hpost
  simpa only [hq0,max_eq_right hr.1,Function.comp_def,v] using H'

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_QuantileOverlapContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFOverlap_continuousOn_quantile {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q ∈ admissibleQuantiles k) :
    ContinuousOn (scalarCDFOverlap β (quantileCDF k Q)) (Icc (0:ℝ) 1) := by
  let q := Fin.snoc (α := fun _ => ℝ) (Fin.cons (α := fun _ => ℝ) 0 Q) (1:ℝ)
  let m := Fin.snoc (α := fun _ => ℝ) (quantileMass k) (1:ℝ)
  have hq : Monotone q := monotone_snoc_one _
    (monotone_cons_zero_quantiles Q hQ.1 (hQ.2 0).1) (by simpa using (hQ.2 (Fin.last k)).2)
  have hq0 : q 0=0 := by simp [q]
  have hq1 : q (Fin.last (k+2))=1 := by simp [q]
  have hm (i : Fin (k+2)) : m i ∈ Icc (0:ℝ) 1 := by
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [m]
    · simpa [m] using quantileMass_bounds k i
  have hmodel (i : Fin (k+2)) (z : ℝ) (hz : z ∈ Ico (q i.castSucc) (q i.succ)) :
      quantileCDF k Q z=m i := by
    revert hz
    refine Fin.lastCases ?_ (fun i => ?_) i
    · intro hz
      simp only [m,Fin.snoc_last]

      apply quantileCDF_of_last_le Q hQ.1
      simpa [q] using hz.1
    · intro hz
      simpa [m] using quantileCDF_on_interval Q hQ.1 i z (by simpa only [q,← Fin.castSucc_succ,Fin.snoc_castSucc,Fin.cons_succ] using hz)
  exact scalarCDFOverlap_continuousOn_partition β (quantileCDF_bounds k Q)
    (quantileCDF_monotone k Q) (k+2) q hq hq0 hq1 m hm hmodel

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFOverlapConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFOverlap_tendstoUniformlyOn (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hn : ∀ n z, αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n, Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n => scalarCDFOverlap β (αn n))
      (scalarCDFOverlap β α) atTop (Icc (0:ℝ) 1) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let h : ℝ := ε/48
  have hh : 0<h := div_pos hε (by norm_num)
  have he : 12*h<ε := by dsimp [h]; linarith
  have hev := (tendsto_order.mp (scalarOverlapModulus_tendsto β h hD)).2 ε he
  filter_upwards [hev] with n hnb x hx
  have H := scalarCDFOverlap_cdf_stability β (hn n) (hnm n) hα hαm hx h hh
  rw [Real.dist_eq,abs_sub_comm]
  exact H.trans_lt hnb

theorem scalarCDFOverlap_continuousOn (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1) :
    ContinuousOn (scalarCDFOverlap β α) (Icc (0:ℝ) 1) := by
  have H := scalarCDFOverlap_tendstoUniformlyOn β ha α.mono
    (fun k => quantileCDF_bounds k (uniformCDFQuantiles k α))
    (fun k => quantileCDF_monotone k (uniformCDFQuantiles k α))
    (uniformCDFQuantiles_L1_tendsto α ha h1)
  apply H.continuousOn
  exact Eventually.frequently (Eventually.of_forall (fun k =>
    scalarCDFOverlap_continuousOn_quantile β (uniformCDFQuantiles k α)
      (uniformCDFQuantiles_admissible k α h1)))

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_SuffixPartitionSusceptibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def scalarCDFSusceptibilityAverage (β : ℝ) (α : ℝ → ℝ) (r : ℝ) : ℝ :=
  scalarCDFAverage β α 0 (Real.toNNReal r)
    (scalarCDFValue β α r (Real.toNNReal (1-r)))
    (scalarCDFHessian β α r (Real.toNNReal (1-r))) 0

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarLevelRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def scalarLevelField : (n : ℕ) → (Fin n → ℝ) → Fin (n+1) → ParameterSpace n →L[ℝ] ℝ
  | 0,_,_ => ContinuousLinearMap.id ℝ ℝ
  | n+1,v,j => Fin.lastCases (scalarSpinField (n+1) v)
      (fun i => (scalarLevelField n (fun k => v k.castSucc) i).comp
        (ContinuousLinearMap.fst ℝ (ParameterSpace n) ℝ)) j

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowMomentBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def narrowSusceptibility (c w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) : ℝ :=
  let f := scalarIncrementChain t scalarSpinTerminal
  vectorIncrementAverage c (fun p : ℝ × ℝ => scalarIncrementChain (weightedUnderlying w) f p.1)
    (vectorIncrementAverage w (fun p : ℝ × ℝ => f p.1) (fun p => rootHessian 0 f p.1)) (0,0)

def narrowMixedMoment (c w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) : ℝ :=
  let f := scalarIncrementChain t scalarSpinTerminal
  let F := scalarIncrementChain (weightedUnderlying w) f
  vectorIncrementAverage c (fun p : ℝ × ℝ => F p.1)
    (fun p => vectorIncrementAverage w (fun p : ℝ × ℝ => f p.1) (fun p => rootHessian 0 f p.1*p.2) p*rootGradient 0 F p.1) (0,0)

def narrowJointMoment (c w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) : ℝ :=
  let f := scalarIncrementChain t scalarSpinTerminal
  let F := scalarIncrementChain (weightedUnderlying w) f
  vectorIncrementAverage c (fun p : ℝ × ℝ => F p.1)
    (fun p => vectorIncrementAverage w (fun p : ℝ × ℝ => f p.1) (fun p => rootHessian 0 f p.1) p*rootHessian 0 F p.1) (0,0)

def narrowTentSquare (c w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) : ℝ :=
  let f := scalarIncrementChain t scalarSpinTerminal
  vectorIncrementAverage c (fun p : ℝ × ℝ => scalarIncrementChain (weightedUnderlying w) f p.1)
    (vectorIncrementAverage w (fun p : ℝ × ℝ => f p.1) (fun p => rootHessian 0 f p.1*p.2^2)) (0,0)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFSquareSusceptibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def scalarCDFSusceptibilitySquareAverage (β : ℝ) (α : ℝ → ℝ) (r : ℝ) : ℝ :=
  scalarCDFAverage β α 0 (Real.toNNReal r)
    (scalarCDFValue β α r (Real.toNNReal (1-r)))
    (fun x => (scalarCDFHessian β α r (Real.toNNReal (1-r)) x)^2) 0

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFJointSusceptibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def scalarCDFConditionalSusceptibility (β : ℝ) (α : ℝ → ℝ) (r q : ℝ) : ℝ → ℝ :=
  scalarCDFAverage β α r (Real.toNNReal (q-r))
    (scalarCDFValue β α q (Real.toNNReal (1-q)))
    (scalarCDFHessian β α q (Real.toNNReal (1-q)))

def scalarCDFJointSusceptibility (β : ℝ) (α : ℝ → ℝ) (r q : ℝ) : ℝ :=
  scalarCDFAverage β α 0 (Real.toNNReal r)
    (scalarCDFValue β α r (Real.toNNReal (1-r)))
    (fun x => scalarCDFHessian β α r (Real.toNNReal (1-r)) x*
      scalarCDFConditionalSusceptibility β α r q x) 0

def scalarCDFJointSusceptibilityTest (β : ℝ) (α : ℝ → ℝ) (r q : ℝ) : ℝ → ℝ :=
  fun x => scalarCDFHessian β α r (Real.toNNReal (1-r)) x*scalarCDFConditionalSusceptibility β α r q x

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowCDFTrial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def narrowCDFTrialCoefficient (β : ℝ) (α : ℝ → ℝ) (r h q a θ : ℝ) : ℝ :=
  β^2*((2*a^2+θ^2)/h)*(scalarCDFSusceptibilityAverage β α q-(∫ x in q..1,α x))+
  2*narrowCDFMean β α r h θ*(β^2*a)*scalarCDFJointSusceptibility β α r q+
  narrowTentError (narrowCDFMean β α r h θ) (β^2*a) (β^2*θ) (α (r+h)-α (r-h))-
  β^2*(α r*(2*a*θ+θ^2)-a^2*(α (r+h)-α (r-h)))

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def scalarCDFPotential (β : ℝ) (α : ℝ → ℝ) (q : ℝ) : ℝ :=
  ∫ s in q..1, -cdfGradientTest β α s

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_QuantileWeakIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def scalarCDFOverlapTest (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ x, α x∈Icc (0:ℝ) 1) (h1 : α 1=1) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => scalarCDFOverlap β α (projIcc 0 1 (by norm_num) x),
      (continuousOn_iff_continuous_domRestrict.mp
        (scalarCDFOverlap_continuousOn β α ha h1)).comp (continuous_projIcc (h := (by norm_num : (0:ℝ)≤1)))⟩ 1 (by
        intro x y
        rw [Real.dist_eq]
        apply abs_le.mpr
        have hx := scalarCDFOverlap_nonneg_le_one β ha α.mono (projIcc 0 1 (by norm_num) x).property
        have hy := scalarCDFOverlap_nonneg_le_one β ha α.mono (projIcc 0 1 (by norm_num) y).property
        change -1 ≤ scalarCDFOverlap β α (projIcc 0 1 (by norm_num) x)-
          scalarCDFOverlap β α (projIcc 0 1 (by norm_num) y) ∧
          scalarCDFOverlap β α (projIcc 0 1 (by norm_num) x)-
            scalarCDFOverlap β α (projIcc 0 1 (by norm_num) y)≤1
        constructor <;> linarith [hx.1,hx.2,hy.1,hy.2])

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_MatrixReplicaBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def matrixReplicaEquiv (n d : ℕ) (D : Fin d → Fin d → ℝ) :
    MatrixStates n d D ≃ {s : ReplicaConfig n d // s∈matrixReplicaSet n d D} where
  toFun s := ⟨fun a i => s.val i a,(mem_matrixReplicaSet D _).mpr s.property⟩
  invFun s := ⟨fun i a => s.val a i,(mem_matrixReplicaSet D _).mp s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_TimeChainAverageAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

@[simp] theorem scalarStepAverage_zero_coefficient (m : ℝ) (f g : ℝ → ℝ) :
    scalarStepAverage m 0 f g=g := by
  funext x
  simp only [scalarStepAverage,gaussianAverage,gaussianStepLaw,zero_mul,add_zero]
  rw [tilted_const,integral_const]
  simp

@[simp] theorem scalarTimeChainAverage_singleton_zero (β m : ℝ) (f g : ℝ → ℝ) :
    scalarTimeChainAverage β [(m,0)] f g=g := by
  change scalarHierarchyAverage 1 (fun _ => m) (fun _ => β*Real.sqrt (0:ℝ)) f g=g
  simp only [Real.sqrt_zero,mul_zero,scalarHierarchyAverage,scalarStepAverage_zero_coefficient]

@[simp] theorem scalarTimeChain_snoc_zero (β m : ℝ) (l : List (ℝ × ℝ≥0)) (f : ℝ → ℝ) :
    scalarTimeChain β (l++[(m,0)]) f=scalarTimeChain β l f := by
  rw [scalarTimeChain_append]
  simp [scalarTimeChain]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_VectorMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section Site
variable {S : Type} [Fintype S] [Nonempty S]

def siteMultiplierExponent (n : ℕ) (V : Fin n → S → ℝ) (O : S → ℝ) (s : S) :
    ParameterSpace n →L[ℝ] ℝ := O s • parameter n+∑ j, V j s • coordinateProjection n j

end Site

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_PairSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def pairIndependentHierarchy : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ) →
    (ℝ × ℝ → ℝ) → ℝ × ℝ → ℝ
  | 0,_,_,f => f
  | n+1,m,v,f => pairIndependentHierarchy n (fun i => m i.castSucc) (fun i => v i.castSucc)
      (pairIndependentStep (m (Fin.last n)) (v (Fin.last n)) f)

def pairIndependentHierarchyAverage : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ) →
    (ℝ × ℝ → ℝ) → (ℝ × ℝ → ℝ) → ℝ × ℝ → ℝ
  | 0,_,_,_,g => g
  | n+1,m,v,f,g => pairIndependentHierarchyAverage n (fun i => m i.castSucc) (fun i => v i.castSucc)
      (pairIndependentStep (m (Fin.last n)) (v (Fin.last n)) f)
      (pairIndependentAverage (m (Fin.last n)) (v (Fin.last n)) f g)

def pairCommonHierarchy : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ) →
    (ℝ × ℝ → ℝ) → ℝ × ℝ → ℝ
  | 0,_,_,f => f
  | n+1,m,v,f => pairCommonHierarchy n (fun i => m i.castSucc) (fun i => v i.castSucc)
      (vectorStep (m (Fin.last n)/2) (v (Fin.last n),v (Fin.last n)) f)

def pairCommonHierarchyAverage : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ) →
    (ℝ × ℝ → ℝ) → (ℝ × ℝ → ℝ) → ℝ × ℝ → ℝ
  | 0,_,_,_,g => g
  | n+1,m,v,f,g => pairCommonHierarchyAverage n (fun i => m i.castSucc) (fun i => v i.castSucc)
      (vectorStep (m (Fin.last n)/2) (v (Fin.last n),v (Fin.last n)) f)
      (vectorStepAverage (m (Fin.last n)/2) (v (Fin.last n),v (Fin.last n)) f g)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_OverlapCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def pairReplicaCode {n : ℕ} (s : ReplicaConfig n 2) : Fin (n+1) := overlapCode (s 0) (s 1)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_PairGibbsGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def pairMismatchSet (n : ℕ) (β : ℝ) (α : ℝ → ℝ) (e : ℝ) : Finset (ReplicaConfig n 2) := by
  classical
  exact Finset.univ.filter (fun s => 0≤overlap (s 0) (s 1) ∧
    e≤|overlap (s 0) (s 1)-scalarCDFOverlap β α (overlap (s 0) (s 1))|)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_SignedLocking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def orientedLockingSet (n : ℕ) (β : ℝ) (α : ℝ → ℝ) (h b τ : ℝ) : Finset (ReplicaConfig n 3) := by
  classical
  exact Finset.univ.filter (fun s => tripleQ s∈Icc h 1 ∧ tripleR s∈Icc (0:ℝ) b ∧
    |tripleDelta s|≤b ∧ (n:ℝ)^(-(1:ℝ)/100)≤|tripleDelta s| ∧
    |tripleQ s-scalarCDFOverlap β α (tripleQ s)|≤τ)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_HighProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def finiteGoodEvent (C : ℕ → (n : ℕ) → Set (Disorder n)) : ℕ → (n : ℕ) → Set (Disorder n)
  | 0,_ => univ
  | j+1,n => finiteGoodEvent C j n ∩ C j n

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_BankPool
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical
namespace SK.Analytic

def orientedBankPool {n p : ℕ} (K : Fin p → ℕ) (z : BankIndex K → Config n) (j : Fin p) : Finset (Config n) :=
  Finset.univ.image (fun a : Fin (K j) × Bool => orient a.2 (z ⟨j,a.1⟩))

def natBankPool {n p : ℕ} (K : Fin p → ℕ) (z : BankIndex K → Config n) (j : ℕ) : Finset (Config n) :=
  if h : j<p then orientedBankPool K z ⟨j,h⟩ else {fun _ => false}

def natBankDefault {n p : ℕ} (K : Fin p → ℕ) (hK : ∀j,0<K j) (z : BankIndex K → Config n) (j : ℕ) : Config n :=
  if h : j<p then z ⟨⟨j,h⟩,⟨0,hK ⟨j,h⟩⟩⟩ else fun _ => false

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_KernelEvents
attribute [-instance] _root_.OAI.SK.disorderPairLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def kernelEvent {n : ℕ} (β : ℝ) (J : Disorder n) (A : Config n → Prop) [DecidablePred A]
    (k : ℕ) (x : Config n) : ℝ := ∑ y : Config n, if A y then discreteKernel β J k x y else 0

def occupation {n : ℕ} (β : ℝ) (J : Disorder n) (A : Config n → Prop) [DecidablePred A]
    (k : ℕ) (x : Config n) : ℝ := ∑ i ∈ Finset.range (k+1), kernelEvent β J A i x

end SK.Analytic

end
end

end

end OAI
end



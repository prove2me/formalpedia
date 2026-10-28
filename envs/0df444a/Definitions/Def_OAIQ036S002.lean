-- Prove2me | Definitions.Def_OAIQ036S002
-- name    : OAIQ036S002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T04:50:00.827992+00:00
-- url     : https://prove2.me/theorems/cf15db44-e1b4-4e4e-ab1e-bbeedfcc25c5
-- title:
--   Definitions bundle OAIQ036S002 of the split of OpenAI, Stretched-exponential barriers for typical SK initial states
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SK.main`, carved from OpenAI's openai/math development (OpenAI, *Stretched-exponential barriers for typical SK initial states*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 278 declarations of OpenAI's Lean: 111 definitions, 2 inductive types or structures, 3 instances and 162 theorems. The definitions and types are `OAI.SK.Analytic.ParameterInvariant`, `OAI.SK.Analytic.PrefixZero`, `OAI.SK.Analytic.RegularConvex`, `OAI.SK.Analytic.RootBoundedCurvature`, `OAI.SK.Analytic.RootSpinCurvature`, `OAI.SK.Analytic.ScalarSpinConvex`, `OAI.SK.Analytic.SmoothFamily.directionalEnergy`, `OAI.SK.Analytic.SmoothFamily.gibbs`, `OAI.SK.Analytic.SmoothFamily.logPartition`, `OAI.SK.Analytic.SmoothFamily.rotationIntegrand`, `OAI.SK.Analytic.TailZero`, `OAI.SK.Analytic.TripleMiddleIncrement`, `OAI.SK.Analytic.TripleTimeBlocks`, `OAI.SK.Analytic.TripleTimeBlocks.a`, `OAI.SK.Analytic.TripleTimeBlocks.b`, `OAI.SK.Analytic.TripleTimeBlocks.c`, `OAI.SK.Analytic.TripleTimeBlocks.d`, `OAI.SK.Analytic.TripleTimeBlocks.early`, `OAI.SK.Analytic.TripleTimeBlocks.front`, `OAI.SK.Analytic.TripleTimeBlocks.full`, `OAI.SK.Analytic.TripleTimeBlocks.t`, `OAI.SK.Analytic.TripleTimeBlocks.w`, `OAI.SK.Analytic.Weighted.Weights`, `OAI.SK.Analytic.Weighted.directionalEnergy`, `OAI.SK.Analytic.Weighted.gibbs`, `OAI.SK.Analytic.Weighted.logPartition`, `OAI.SK.Analytic.Weighted.partition`, `OAI.SK.Analytic.Weighted.rotationIntegrand`, `OAI.SK.Analytic.affineHierarchyResponse`, `OAI.SK.Analytic.atomicParisi`, `OAI.SK.Analytic.atomicScalarValue`, `OAI.SK.Analytic.bankBadVertex`, `OAI.SK.Analytic.bankCell`, `OAI.SK.Analytic.bankCoverageBad`, `OAI.SK.Analytic.bankJointIndex`, `OAI.SK.Analytic.bankPick`, `OAI.SK.Analytic.bankTripleBad`, `OAI.SK.Analytic.bankVertexBad`, `OAI.SK.Analytic.blockAdaptiveOverlap`, `OAI.SK.Analytic.blockExponent` and 73 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability/SKBarriers, in whole or in part: `SKBarriers_Calculus_CoordinateGaussianLaw`, `SKBarriers_Calculus_CoordinateSigns`, `SKBarriers_Calculus_CoordinateStein`, `SKBarriers_Calculus_CubeMeasures`, `SKBarriers_Calculus_ParameterAlgebra`, `SKBarriers_Calculus_ParameterAverage`, `SKBarriers_Calculus_ParameterCalculus`, `SKBarriers_Calculus_ParameterDerivatives`, `SKBarriers_Calculus_ParameterFieldMap`, `SKBarriers_Calculus_ParameterProduct`, `SKBarriers_Calculus_ParameterRecursion`, `SKBarriers_Calculus_ParameterSmooth`, `SKBarriers_Calculus_ParameterSpace`, `SKBarriers_Coverage_FiniteCoverage`, `SKBarriers_Coverage_UniformCoverage`, `SKBarriers_Coverage_WeightedConcentration`, `SKBarriers_Dynamics_BankAvoidance`, `SKBarriers_Dynamics_BankCardinality`, `SKBarriers_Dynamics_BankCoverage`, `SKBarriers_Dynamics_BankDynamics`, `SKBarriers_Dynamics_ClockEndpoint`, `SKBarriers_Dynamics_GreedyRecursion`, `SKBarriers_Dynamics_HeatBathEnergy`, `SKBarriers_Dynamics_PathEndpoint`, `SKBarriers_Gaussian_BlockStein`, `SKBarriers_Gaussian_BoundedObservableCurvature`, `SKBarriers_Gaussian_BoundedPrimitive`, `SKBarriers_Gaussian_GaussianAverage`, `SKBarriers_Gaussian_GaussianCovarianceStep`, `SKBarriers_Gaussian_GaussianGrowth`, `SKBarriers_Gaussian_GaussianMassDerivative`, `SKBarriers_Gaussian_GaussianMassStability`, `SKBarriers_Gaussian_GaussianResponse`, `SKBarriers_Gaussian_GaussianSecondStep`, `SKBarriers_Gaussian_GaussianSpinTrace`, `SKBarriers_Gaussian_GaussianStepAlgebra`, `SKBarriers_Gaussian_GaussianStepCalculus`, `SKBarriers_Gaussian_GaussianZeroMass`, `SKBarriers_Gaussian_SmoothFamily`, `SKBarriers_Hierarchy_AverageMeanVariance`, `SKBarriers_Hierarchy_BlockAdaptiveOverlap`, `SKBarriers_Hierarchy_CascadeBlockLaw`, `SKBarriers_Hierarchy_CascadeProbability`, `SKBarriers_Hierarchy_CascadeRebase`, `SKBarriers_Hierarchy_CascadeRecursion`, `SKBarriers_Hierarchy_HierarchyBlocks`, `SKBarriers_Hierarchy_HierarchyDensity`, `SKBarriers_Hierarchy_HierarchyIncrementCovariance`, `SKBarriers_Hierarchy_HierarchyJointMoment`, `SKBarriers_Hierarchy_HierarchyLevels`, `SKBarriers_Hierarchy_HierarchyMomentLevels`, `SKBarriers_Hierarchy_HierarchyPathLaw`, `SKBarriers_Hierarchy_HierarchyPenalty`, `SKBarriers_Hierarchy_HierarchyPrefix`, `SKBarriers_Hierarchy_RootCalculus`, `SKBarriers_Hierarchy_RootGeneralCurvature`, `SKBarriers_Hierarchy_RootHessianIdentity`, `SKBarriers_Hierarchy_RootSusceptibility`, `SKBarriers_Hierarchy_RootTranslation`, `SKBarriers_Hierarchy_TimeChainRepresentation`, `SKBarriers_Hierarchy_TimeChainSplit`, `SKBarriers_Hierarchy_WeightedBlockFactors`, `SKBarriers_Locking_NarrowGibbsGap`, `SKBarriers_Locking_SignedLocking`, `SKBarriers_Parisi_CDFOverlap`, `SKBarriers_Replicas_MatrixReplicaBridge`, `SKBarriers_Replicas_ReplicaCoordinates`, `SKBarriers_Replicas_ReplicaFlip`, `SKBarriers_Replicas_ReplicaSampling`, `SKBarriers_Replicas_TripleSchedule`, `SKBarriers_Replicas_TripleTimeBlocks`, `SKBarriers_Scalar_DyadicCDFStability`, `SKBarriers_Scalar_DyadicScalar`, `SKBarriers_Scalar_DyadicSpin`, `SKBarriers_Scalar_GeneralCDFStability`, `SKBarriers_Scalar_OneSiteScalar`, `SKBarriers_Scalar_OverlapModulus`, `SKBarriers_Scalar_PrefixAlgebra`, `SKBarriers_Scalar_ScalarAtomic`, `SKBarriers_Scalar_ScalarAverageCalculus`, `SKBarriers_Scalar_ScalarCDFLimit`, `SKBarriers_Scalar_ScalarCurvature`, `SKBarriers_Scalar_ScalarGeneralTerminal`, `SKBarriers_Scalar_ScalarHierarchy`, `SKBarriers_Scalar_ScalarHierarchyMass`, `SKBarriers_Scalar_ScalarMassOne`, `SKBarriers_Scalar_ScalarMassStability`, `SKBarriers_Scalar_ScalarSemigroup`, `SKBarriers_Scalar_ScalarSpinRecursion`, `SKBarriers_Scalar_ScalarTiltedExpectation`, `SKBarriers_Scalar_ScalarTimeChain`, `SKBarriers_Scalar_TerminalPerturbation`, `SKBarriers_Scalar_ThermalMoments`, `SKBarriers_Scalar_TiltedTerminalLimit`, `SKBarriers_SpinGlass_FinitePartition`, `SKBarriers_SpinGlass_SpinMonomials`, `SKBarriers_SpinGlass_SpinSiteTensorization`.
--
--   **Imports.** It imports the published bundle `Def_SKBarriers`; the bundles `OAIQ036S000` and `OAIQ036S001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ036S004` and `OAIQ036S005`; the statements `OAI.SK.Analytic.identity_main_of_static_locking` and `OAI.SK.Analytic.signed_small_scale`.
-- source:
--   OpenAI, Stretched-exponential barriers for typical SK initial states, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Stretched-exponential-barriers-for-typical-SK-initial-states-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability/SKBarriers at commit adc7f12

import Mathlib
import Definitions.Def_SKBarriers
import Definitions.Def_OAIQ036S000
import Definitions.Def_OAIQ036S001

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianZeroMass
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
section ZeroMass
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def RegularConvex (f : E → ℝ) : Prop := BoundedDerivs f ∧ ConvexOn ℝ univ f

end ZeroMass
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
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianStepCalculus
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
section StepCalculus
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem gaussianStepLaw_probability {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (m : ℝ) (x : E) : IsProbabilityMeasure (gaussianStepLaw m f x) :=
  isProbabilityMeasure_tilted (hf.exp_integrable m x)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem gaussianStepLaw_zero (f : E × ℝ → ℝ) (x : E) :
    gaussianStepLaw 0 f x = gaussianReal 0 1 := by
  simp [gaussianStepLaw]

theorem fderiv_gaussianStep {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (m : ℝ) (x : E) :
    fderiv ℝ (gaussianStep m f) x =
      ∫ y, leftRestrict (fderiv ℝ f (x,y)) ∂gaussianStepLaw m f x := by
  classical
  obtain ⟨hfd,C,D,hC,hD,hb,hbb⟩ := hf
  have hd := hfd.differentiable (by norm_num)
  have hg := exp_mul_growth_of_fderiv_bound f hd C hC hb m
  have hmf : BoundedDerivs (fun z => m*f z) :=
    BoundedDerivs.const_mul ⟨hfd,C,D,hC,hD,hb,hbb⟩ m
  have hmfb : ∀ z, ‖fderiv ℝ (fun z => m*f z) z‖ ≤ |m| * C := by
    intro z
    rw [((hd z).hasFDerivAt.const_mul m).fderiv, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hb z) (abs_nonneg m)
  have hg₁ := fderiv_exp_growth _ (hmf.1.differentiable (by norm_num)) hg
    (mul_nonneg (abs_nonneg m) hC) hmfb
  by_cases hm : m = 0
  · subst m
    rw [gaussianStepLaw_zero]
    have he : SK.Analytic.gaussianStep 0 f = (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) := by
      funext x
      simp only [SK.Analytic.gaussianStep,ite_true]
    rw [he]
    exact fderiv_gaussian_integral f (hfd.of_le (by norm_num))
      (growth_of_fderiv_bound f hd hC hb)
      (HasExpGrowth.of_bounded hC hb) x
  · let Z : E → ℝ := fun x => ∫ y, Real.exp (m*f (x,y)) ∂gaussianReal 0 1
    have hZ := hmf.exp_smooth_integral
    have hp : Z x ≠ 0 := (integral_exp_pos
      (BoundedDerivs.exp_integrable ⟨hfd,C,D,hC,hD,hb,hbb⟩ m x)).ne'
    have he : gaussianStep m f = fun x => Real.log (Z x)/m := by
      funext x
      simp only [gaussianStep,ite_eq_right hm,positiveGaussianLogStep,Z]
    rw [he]
    have hder := ((hZ.differentiable (by norm_num) x).hasFDerivAt.log hp).mul_const m⁻¹
    simp only [div_eq_mul_inv] at ⊢
    rw [hder.fderiv]
    have hi := fderiv_gaussian_integral (fun z => Real.exp (m*f z))
      ((contDiff_const.mul hfd).exp.of_le (by norm_num)) hg hg₁ x
    change (m⁻¹ • ((Z x)⁻¹ • fderiv ℝ Z x)) = _
    rw [hi,← integral_smul,← integral_smul,gaussianStepLaw,integral_tilted]
    apply integral_congr_ae
    filter_upwards [] with y
    have hdexp := ((hd (x,y)).hasFDerivAt.const_mul m).exp.fderiv
    rw [hdexp]
    ext v
    simp only [smul_apply,smul_eq_mul,leftRestrict,
      ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply]
    dsimp only [Z] at hp ⊢
    field_simp [hm,hp]

end StepCalculus
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
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_ParameterSpace
attribute [-instance] _root_.OAI.SK.Analytic.fiberGaussian_isGaussian _root_.OAI.SK.Analytic.parameterBorel _root_.OAI.SK.Analytic.parameterMeasurable _root_.OAI.SK.Analytic.parameterSecondCountable
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

def cubePotential : (n : ℕ) → (ParameterSpace n → ℝ) → ℝ → ℝ → ℝ → ℝ
  | 0, V, _, _ => V
  | n+1, V, a, b => cubePotential n (marginalPotential V a b) a b

end SK.Analytic

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_ParameterCalculus
attribute [-instance] _root_.OAI.SK.Analytic.fiberGaussian_isGaussian _root_.OAI.SK.Analytic.parameterBorel _root_.OAI.SK.Analytic.parameterMeasurable _root_.OAI.SK.Analytic.parameterSecondCountable
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

@[simp] theorem coordinateSquare_axis (n : ℕ) : coordinateSquare n (parameterAxis n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [coordinateSquare, parameterAxis, pow_two, mul_zero, add_zero] using ih

def cubeIntegral : (n : ℕ) → (ParameterSpace n → ℝ) → ℝ → ℝ → ℝ → ℝ
  | 0, f, _, _ => f
  | n+1, f, a, b => cubeIntegral n (fun x => ∫ y in a..b, f (x,y)) a b

end SK.Analytic

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_CubeMeasures
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
namespace SK.Analytic

def cubeMeasure : (n : ℕ) → ℝ → ℝ → ℝ → Measure (ParameterSpace n)
  | 0, x, _, _ => Measure.dirac x
  | n+1, x, a, b => (cubeMeasure n x a b).prod (volume.restrict (Ioc a b))

instance cubeFiniteMeasure : (n : ℕ) → (x a b : ℝ) → IsFiniteMeasure (cubeMeasure n x a b)
  | 0, x, _, _ => inferInstanceAs (IsFiniteMeasure (Measure.dirac x))
  | n+1, x, a, b => letI := cubeFiniteMeasure n x a b
                    inferInstanceAs (IsFiniteMeasure ((cubeMeasure n x a b).prod (volume.restrict (Ioc a b))))

def cubeSupport : (n : ℕ) → ℝ → ℝ → ℝ → Set (ParameterSpace n)
  | 0, x, _, _ => {x}
  | n+1, x, a, b => (cubeSupport n x a b) ×ˢ Icc a b

def cubeSet : (n : ℕ) → ℝ → ℝ → Set (ParameterSpace n)
  | 0, _, _ => univ
  | n+1, a, b => cubeSet n a b ×ˢ Ioc a b

end SK.Analytic

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_FinitePartition
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
section FinitePartition
variable {E S : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype S] [Nonempty S]

theorem affineLogPartition_boundedDerivs (c : S → ℝ) (L : S → E →L[ℝ] ℝ) :
    BoundedDerivs (affineLogPartition c L) := by
  classical
  let Z : E → ℝ := fun x => ∑ s, Real.exp (c s+L s x)
  let Z₁ : E → E →L[ℝ] ℝ := fun x => ∑ s, Real.exp (c s+L s x) • L s
  let Z₂ : E → E →L[ℝ] E →L[ℝ] ℝ := fun x =>
    ∑ s, (Real.exp (c s+L s x) • L s).smulRight (L s)
  have hd (s : S) (x : E) : HasFDerivAt (fun x => c s+L s x) (L s) x := by
    simpa only [zero_add] using (hasFDerivAt_const (c s) x).fun_add (L s).hasFDerivAt
  have hz₁ (x : E) : HasFDerivAt Z (Z₁ x) x := by
    exact HasFDerivAt.fun_sum (fun s _ => (hd s x).exp)
  have hz₂ (x : E) : HasFDerivAt Z₁ (Z₂ x) x := by
    exact HasFDerivAt.fun_sum (fun s _ => (hd s x).exp.smul_const (L s))
  have he : fderiv ℝ Z = Z₁ := funext (fun x => (hz₁ x).fderiv)
  have he₂ : fderiv ℝ (fderiv ℝ Z) = Z₂ := by
    rw [he]
    exact funext (fun x => (hz₂ x).fderiv)
  have hc : ContDiff ℝ 2 Z := by
    apply ContDiff.sum
    intro s _
    exact (contDiff_const.add (L s).contDiff).exp
  have hp (x : E) : 0 < Z x := Finset.sum_pos (fun s _ => Real.exp_pos _) Finset.univ_nonempty
  let C : ℝ := ∑ s, ‖L s‖
  have hC : 0 ≤ C := Finset.sum_nonneg fun s _ => norm_nonneg _
  have hL (s : S) : ‖L s‖ ≤ C := Finset.single_le_sum (fun t _ => norm_nonneg (L t)) (Finset.mem_univ s)
  change BoundedDerivs (fun x => Real.log (Z x))
  apply log_boundedDerivs_of_relative_bounds Z hc hp hC (mul_nonneg hC hC)
  · intro x
    rw [he]
    apply (norm_sum_le _ _).trans
    change (∑ s, ‖Real.exp (c s+L s x) • L s‖) ≤ C*∑ s, Real.exp (c s+L s x)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left (hL s) (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  · intro x
    rw [he₂]
    apply (norm_sum_le Finset.univ (fun s : S =>
      (Real.exp (c s+L s x) • L s).smulRight (L s))).trans
    change (∑ s, ‖(Real.exp (c s+L s x) • L s).smulRight (L s)‖) ≤
      (C*C)*∑ s, Real.exp (c s+L s x)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s _
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (Real.exp (c s+L s x)*C)*C := by gcongr <;> exact hL s
      _ = _ := by ring

end FinitePartition
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
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyPenalty
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

def hierarchyPenalty : (n : ℕ) → (Fin n → ℝ) → ℝ →
    (ParameterSpace n → ℝ) → ParameterSpace n → ℝ
  | 0, _, u, f, z => u*f z
  | n+1, m, u, f, z =>
      (u-m (Fin.last n))*f z +
      hierarchyPenalty n (fun i => m i.castSucc) (m (Fin.last n))
        (gaussianStep (m (Fin.last n)) f) z.1

def hierarchyPathWeight : (n : ℕ) → (Fin n → ℝ) →
    (ParameterSpace n → ℝ) → ParameterSpace n → ℝ
  | 0, _, _, _ => 1
  | n+1, m, f, z =>
      Real.exp (m (Fin.last n)*(f z-gaussianStep (m (Fin.last n)) f z.1)) *
      hierarchyPathWeight n (fun i => m i.castSucc)
        (gaussianStep (m (Fin.last n)) f) z.1

def ParameterInvariant (n : ℕ) (f : ParameterSpace n → ℝ) : Prop :=
  ∀ (z : ParameterSpace n) (t : ℝ), f (z+t • parameterAxis n) = f z

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
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_CoordinateSigns
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

def coordinateSign : (n : ℕ) → (Fin n → Bool) → ParameterSpace n → ParameterSpace n
  | 0, _, z => z
  | n+1, b, z => (coordinateSign n (fun i => b i.castSucc) z.1,scalarSign (b (Fin.last n)) z.2)

theorem coordinateSign_involutive (n : ℕ) (b : Fin n → Bool) :
    Function.Involutive (coordinateSign n b) := by
  induction n with
  | zero => intro z; rfl
  | succ n ih =>
    intro z
    change (coordinateSign n (fun i => b i.castSucc)
      (coordinateSign n (fun i => b i.castSucc) z.1),
      scalarSign (b (Fin.last n)) (scalarSign (b (Fin.last n)) z.2)) = z
    rw [ih _ z.1, scalarSign_involutive]

theorem coordinateSign_continuous (n : ℕ) (b : Fin n → Bool) :
    Continuous (coordinateSign n b) := by
  induction n with
  | zero => exact continuous_id
  | succ n ih =>
    exact ((ih _).comp continuous_fst).prodMk ((scalarSign_continuous _).comp continuous_snd)

def coordinateSignEquiv (n : ℕ) (b : Fin n → Bool) : ParameterSpace n ≃ᵐ ParameterSpace n where
  toFun := coordinateSign n b
  invFun := coordinateSign n b
  left_inv := coordinateSign_involutive n b
  right_inv := coordinateSign_involutive n b
  measurable_toFun := (coordinateSign_continuous n b).measurable
  measurable_invFun := (coordinateSign_continuous n b).measurable

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

def coordinateProjection : (n : ℕ) → Fin n → ParameterSpace n →L[ℝ] ℝ
  | 0, i => Fin.elim0 i
  | n+1, i => Fin.lastCases (ContinuousLinearMap.snd ℝ (ParameterSpace n) ℝ)
      (fun j => (coordinateProjection n j).comp (ContinuousLinearMap.fst ℝ (ParameterSpace n) ℝ)) i

@[simp] theorem coordinateProjection_last (n : ℕ) (z : ParameterSpace (n+1)) :
    coordinateProjection (n+1) (Fin.last n) z = z.2 := by simp [coordinateProjection]

@[simp] theorem coordinateProjection_castSucc (n : ℕ) (i : Fin n) (z : ParameterSpace (n+1)) :
    coordinateProjection (n+1) i.castSucc z = coordinateProjection n i z.1 := by
  simp [coordinateProjection]

theorem coordinateProjection_axis (n : ℕ) (i : Fin n) :
    coordinateProjection n i (parameterAxis n) = 0 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [coordinateProjection,parameterAxis]
    · simpa only [coordinateProjection,Fin.lastCases_castSucc,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst',parameterAxis] using ih j

def coordinateLinear (n : ℕ) (a : Fin n → ℝ) : ParameterSpace n →L[ℝ] ℝ :=
  ∑ i, a i • coordinateProjection n i

theorem coordinateLinear_apply (n : ℕ) (a : Fin n → ℝ) (z : ParameterSpace n) :
    coordinateLinear n a z = ∑ i, a i*coordinateProjection n i z := by
  simp [coordinateLinear]

theorem coordinateLinear_axis (n : ℕ) (a : Fin n → ℝ) :
    coordinateLinear n a (parameterAxis n) = 0 := by
  simp [coordinateLinear_apply,coordinateProjection_axis]

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
attribute [-instance] _root_.OAI.SK.Analytic.fiberGaussian_isGaussian
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

def coordinateArray (n : ℕ) (z : ParameterSpace n) : Fin n → ℝ :=
  fun i => coordinateProjection n i z

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianGrowth
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

def coordinateAxis : (n : ℕ) → Fin n → ParameterSpace n
  | 0, i => Fin.elim0 i
  | n+1, i => Fin.lastCases (0,1) (fun j => (coordinateAxis n j,0)) i

@[simp] theorem coordinateAxis_last (n : ℕ) : coordinateAxis (n+1) (Fin.last n) = (0,1) := by
  simp [coordinateAxis]

@[simp] theorem coordinateAxis_castSucc (n : ℕ) (i : Fin n) :
    coordinateAxis (n+1) i.castSucc = (coordinateAxis n i,0) := by simp [coordinateAxis]

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
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianSecondStep
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
section SecondStep
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_fderiv_gaussianStep_nonzero {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    {m : ℝ} (hm : m ≠ 0) (x : E) :
    fderiv ℝ (fderiv ℝ (gaussianStep m f)) x =
      m⁻¹ • (((∫ y, Real.exp (m*f (x,y)) ∂gaussianReal 0 1)⁻¹) •
        (∫ y, secondLeftRestrict (fderiv ℝ (fderiv ℝ (fun z => Real.exp (m*f z))) (x,y))
          ∂gaussianReal 0 1) +
      (-((∫ y, Real.exp (m*f (x,y)) ∂gaussianReal 0 1)^2)⁻¹ •
        (∫ y, leftRestrict (fderiv ℝ (fun z => Real.exp (m*f z)) (x,y)) ∂gaussianReal 0 1)).smulRight
        (∫ y, leftRestrict (fderiv ℝ (fun z => Real.exp (m*f z)) (x,y)) ∂gaussianReal 0 1)) := by
  let Z : E → ℝ := fun x => ∫ y, Real.exp (m*f (x,y)) ∂gaussianReal 0 1
  have hZ := (hf.const_mul m).exp_smooth_integral
  have hp (z : E) : Z z ≠ 0 := (integral_exp_pos (hf.exp_integrable m z)).ne'
  have he : gaussianStep m f = fun z => m⁻¹*Real.log (Z z) := by
    funext z
    simp only [gaussianStep,ite_eq_right hm,positiveGaussianLogStep,Z,div_eq_mul_inv,mul_comm]
  have hL : ContDiff ℝ 2 (fun z => Real.log (Z z)) := hZ.log hp
  obtain ⟨hg,hg₁,hg₂⟩ := hf.exp_growths m
  rw [he,fderiv_fderiv_const_mul _ hL,fderiv_fderiv_log _ hZ hp]
  rw [fderiv_gaussian_integral _ ((contDiff_const.mul hf.1).exp.of_le (by norm_num)) hg hg₁]
  rw [fderiv_fderiv_gaussian_integral _ (contDiff_const.mul hf.1).exp hg hg₁ hg₂]

theorem fderiv_fderiv_gaussianStep_zero {f : E × ℝ → ℝ} (hf : BoundedDerivs f) (x : E) :
    fderiv ℝ (fderiv ℝ (gaussianStep 0 f)) x =
      ∫ y, secondLeftRestrict (fderiv ℝ (fderiv ℝ f) (x,y)) ∂gaussianReal 0 1 := by
  have he : gaussianStep 0 f = fun x => ∫ y, f (x,y) ∂gaussianReal 0 1 := by
    funext z
    simp only [gaussianStep,ite_true]
  rw [he]
  obtain ⟨hfd,C,D,hC,hD,hb,hbb⟩ := hf
  exact fderiv_fderiv_gaussian_integral f hfd
    (growth_of_fderiv_bound f (hfd.differentiable (by norm_num)) hC hb)
    (HasExpGrowth.of_bounded hC hb) (HasExpGrowth.of_bounded hD hbb) x

theorem integrable_exp_smul_of_bounded {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × ℝ → ℝ} (hf : BoundedDerivs f) (m : ℝ) (x : E)
    (g : ℝ → F) (hg : Continuous g) {C : ℝ} (hb : ∀ y, ‖g y‖ ≤ C) :
    Integrable (fun y => Real.exp (m*f (x,y)) • g y) (gaussianReal 0 1) := by
  apply ((hf.exp_integrable m x).const_mul C).mono'
    ((Real.continuous_exp.comp (continuous_const.mul
      (hf.1.continuous.comp (continuous_const.prodMk continuous_id)))).smul hg).aestronglyMeasurable
  filter_upwards [] with y
  change ‖Real.exp (m*f (x,y)) • g y‖ ≤ C * Real.exp (m*f (x,y))
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_left (hb y) (Real.exp_pos _).le).trans_eq (mul_comm _ _)

end SecondStep
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
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_CoordinateStein
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

def coordinateVector (n : ℕ) (a : Fin n → ℝ) : ParameterSpace n :=
  ∑ i, a i • coordinateAxis n i

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
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_ParameterDerivatives
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
section ParameterDerivatives
variable {P E X : Type} [NormedAddCommGroup P] [NormedAddCommGroup E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

variable {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem param_second_log_growth (f : X → ℝ) (ι : P × E → X) (hf : ContDiff ℝ 2 f)
    (hp : ∀ x, f x ≠ 0) (hg : ParamExpGrowth (fun z => (f (ι z))⁻¹))
    (hg₁ : ParamExpGrowth (fun z => fderiv ℝ f (ι z)))
    (hg₂ : ParamExpGrowth (fun z => fderiv ℝ (fderiv ℝ f) (ι z))) :
    ParamExpGrowth (fun z => fderiv ℝ (fderiv ℝ (fun x => Real.log (f x))) (ι z)) := by
  have H := (hg.smul hg₂).add (((hg.mul hg).neg.smul hg₁).smulRight hg₁)
  simpa only [fderiv_fderiv_log f hf hp,pow_two,mul_inv_rev,neg_mul] using H
end ParameterDerivatives
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_ParameterSmooth
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
section ParameterSmooth
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem param_gaussian_smooth (f : P × (E × ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (hg : ParamExpGrowth f) (hg₁ : ParamExpGrowth (fderiv ℝ f))
    (hg₂ : ParamExpGrowth (fderiv ℝ (fderiv ℝ f))) :
    let Z := fun z : P × E => ∫ y, f (z.1,(z.2,y)) ∂gaussianReal 0 1
    ContDiff ℝ 2 Z ∧ ParamExpGrowth (fderiv ℝ Z) ∧
      ParamExpGrowth (fderiv ℝ (fderiv ℝ Z)) := by
  let L : (P × E) × ℝ →L[ℝ] P × (E × ℝ) :=
    (ContinuousLinearEquiv.prodAssoc ℝ P E ℝ).toContinuousLinearMap
  let ι : P × (E × ℝ) → (P × E) × ℝ := fun z => ((z.1,z.2.1),z.2.2)
  let g := fun z => f (L z)
  have hc : ContDiff ℝ 2 g := hf.comp L.contDiff
  have hg' : ParamExpGrowth (fun z => g (ι z)) := hg
  have h₁ : ParamExpGrowth (fun z => fderiv ℝ g (ι z)) :=
    param_fderiv_compCLM_growth f L ι (hf.differentiable (by norm_num)) hg₁
  have h₂ : ParamExpGrowth (fun z => fderiv ℝ (fderiv ℝ g) (ι z)) :=
    param_second_compCLM_growth f L ι hf hg₂
  exact ⟨param_contDiff_gaussian_integral g hc hg' h₁ h₂,
    param_fderiv_gaussian_integral_growth g (hc.of_le (by norm_num)) hg' h₁,
    param_second_gaussian_integral_growth g hc hg' h₁ h₂⟩

theorem ParamRegular.gaussian_integral {f : P × (E × ℝ) → ℝ} (hf : ParamRegular f) :
    ParamRegular (fun z : P × E => ∫ y, f (z.1,(z.2,y)) ∂gaussianReal 0 1) := by
  have h := param_gaussian_smooth f hf.1 hf.2.1.expGrowth hf.2.2.1 hf.2.2.2
  exact ⟨h.1,hf.2.1.gaussian_integral,h.2⟩
end ParameterSmooth
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

theorem paramSmooth_const (c : ℝ) : ParamSmooth (fun _ : P × E => c) := by
  refine ⟨contDiff_const,?_,?_,?_⟩
  · exact ParamExpGrowth.of_bounded (norm_nonneg c) (fun _ => le_rfl)
  · exact ParamExpGrowth.of_bounded (C := 0) le_rfl (by intro z; simp)
  · have he : fderiv ℝ (fun _ : P × E => c) = fun _ => (0 : P × E →L[ℝ] ℝ) := by
      funext z
      simp
    rw [he]
    intro R
    refine ⟨0,0,le_rfl,le_rfl,?_⟩
    intro p e _
    simp only [fderiv_const_apply,ContinuousLinearMap.opNorm_zero,zero_mul,le_refl]

theorem ParamSmooth.sum {ι : Type} (s : Finset ι) (f : ι → P × E → ℝ)
    (hf : ∀ i ∈ s, ParamSmooth (f i)) : ParamSmooth (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (paramSmooth_const (P := P) (E := E) 0)
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using (hf a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

end ParameterAlgebra
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_ParameterProduct
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

section ParameterProduct
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ParamSmooth.mul {f g : P × E → ℝ} (hf : ParamSmooth f) (hg : ParamSmooth g) :
    ParamSmooth (fun z => f z*g z) := by
  have hd := hf.1.differentiable (by norm_num)
  have he := hg.1.differentiable (by norm_num)
  have hdd := (hf.1.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hee := (hg.1.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h₁ : fderiv ℝ (fun z => f z*g z) = fun z =>
      f z • fderiv ℝ g z+g z • fderiv ℝ f z := by
    funext z
    exact ((hd z).hasFDerivAt.fun_mul (he z).hasFDerivAt).fderiv
  have h₂ : fderiv ℝ (fderiv ℝ (fun z => f z*g z)) = fun z =>
      (f z • fderiv ℝ (fderiv ℝ g) z+(fderiv ℝ f z).smulRight (fderiv ℝ g z))+
      (g z • fderiv ℝ (fderiv ℝ f) z+(fderiv ℝ g z).smulRight (fderiv ℝ f z)) := by
    rw [h₁]
    funext z
    exact (((hd z).hasFDerivAt.fun_smul (hee z).hasFDerivAt).fun_add
      ((he z).hasFDerivAt.fun_smul (hdd z).hasFDerivAt)).fderiv
  refine ⟨hf.1.mul hg.1,hf.2.1.mul hg.2.1,?_,?_⟩
  · rw [h₁]
    exact (hf.2.1.smul hg.2.2.1).add (hg.2.1.smul hf.2.2.1)
  · rw [h₂]
    exact ((hf.2.1.weakSmul hg.2.2.2 (fun _ => ContinuousLinearMap.opNorm_nonneg _)
      (fun _ => ContinuousLinearMap.opNorm_smul_le _ _)).weakAdd (hf.2.2.1.smulRight hg.2.2.1)
      (fun _ => ContinuousLinearMap.opNorm_add_le _ _)).weakAdd
      ((hg.2.1.weakSmul hf.2.2.2 (fun _ => ContinuousLinearMap.opNorm_nonneg _)
        (fun _ => ContinuousLinearMap.opNorm_smul_le _ _)).weakAdd (hg.2.2.1.smulRight hf.2.2.1)
        (fun _ => ContinuousLinearMap.opNorm_add_le _ _))
      (fun _ => ContinuousLinearMap.opNorm_add_le _ _)

theorem ParamSmooth.const_mul {f : P × E → ℝ} (hf : ParamSmooth f) (c : ℝ) :
    ParamSmooth (fun z => c*f z) := (paramSmooth_const c).mul hf

theorem ParamSmooth.gaussian_integral {f : P × (E × ℝ) → ℝ} (hf : ParamSmooth f) :
    ParamSmooth (fun z : P × E => ∫ y, f (z.1,(z.2,y)) ∂gaussianReal 0 1) := by
  have h := param_gaussian_smooth f hf.1 hf.2.1 hf.2.2.1 hf.2.2.2
  exact ⟨h.1,hf.2.1.gaussian_integral,h.2⟩
end ParameterProduct
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_ParameterRecursion
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
section ParameterRecursion
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ParamRegular.log_gaussian_exp {f : P × (E × ℝ) → ℝ} (hf : ParamRegular f) :
    ParamRegular (fun z : P × E => Real.log
      (∫ y, Real.exp (f (z.1,(z.2,y))) ∂gaussianReal 0 1)) := by
  have hg : ParamExpGrowth (fun z => Real.exp (f z)) := by
    simpa only [one_mul] using hf.2.1.exp_mul 1
  have h₁ := param_fderiv_exp_growth f id (hf.1.differentiable (by norm_num)) hg hf.2.2.1
  have h₂ := param_second_exp_growth f id hf.1 hg hf.2.2.1 hf.2.2.2
  let Z := fun z : P × E => ∫ y, Real.exp (f (z.1,(z.2,y))) ∂gaussianReal 0 1
  have hZ := param_gaussian_smooth (fun z => Real.exp (f z)) hf.1.exp hg h₁ h₂
  have hp (z : P × E) : Z z ≠ 0 := by
    apply (integral_exp_pos _).ne'
    apply hg.weakLocallyDominated.integrable_section
    exact Real.continuous_exp.comp (hf.1.continuous.comp
      (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd)))
  have hi : ParamExpGrowth (fun z => (Z z)⁻¹) := hf.2.1.inv_gaussian_exp hf.1.continuous
  exact ⟨hZ.1.log hp,hf.2.1.log_gaussian_exp hf.1.continuous,
    param_fderiv_log_growth Z id (hZ.1.differentiable (by norm_num)) hp hi hZ.2.1,
    param_second_log_growth Z id hZ.1 hp hi hZ.2.1 hZ.2.2⟩

theorem ParamRegular.gaussianStep {f : P × (E × ℝ) → ℝ} (hf : ParamRegular f) (m : ℝ) :
    ParamRegular (gaussianStep m (fun z : (P × E) × ℝ => f (z.1.1,(z.1.2,z.2)))) := by
  change ParamRegular (fun z : P × E => if m = 0 then
    ∫ y, f (z.1,(z.2,y)) ∂gaussianReal 0 1 else
    Real.log (∫ y, Real.exp (m*f (z.1,(z.2,y))) ∂gaussianReal 0 1) / m)
  by_cases hm : m = 0
  · subst m
    simpa only [ite_true] using hf.gaussian_integral
  · have H := ((hf.const_mul m).log_gaussian_exp).const_mul m⁻¹
    simpa only [ite_eq_right hm,div_eq_mul_inv,mul_comm] using H
end ParameterRecursion
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianCovarianceStep
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
section CovarianceStep
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem gaussianStepLaw_integral_inv_smul {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m : ℝ) (f : E × ℝ → ℝ) (x : E) (g : ℝ → F) :
    (∫ y, g y ∂gaussianStepLaw m f x) =
      (∫ y, Real.exp (m*f (x,y)) ∂gaussianReal 0 1)⁻¹ •
        ∫ y, Real.exp (m*f (x,y)) • g y ∂gaussianReal 0 1 := by
  rw [gaussianStepLaw,integral_tilted,← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [smul_smul,div_eq_mul_inv,mul_comm]

attribute [local instance] OAI.SK.Analytic.instSMulZeroClassRealContinuousLinearMapId_solutions
attribute [local instance] OAI.SK.Analytic.instIsBoundedSMulRealContinuousLinearMapId_solutions
theorem fderiv_fderiv_gaussianStep {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (m : ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ (gaussianStep m f)) x =
      (∫ y, secondLeftRestrict (fderiv ℝ (fderiv ℝ f) (x,y)) ∂gaussianStepLaw m f x) +
      m • ((∫ y, (leftRestrict (fderiv ℝ f (x,y))).smulRight
          (leftRestrict (fderiv ℝ f (x,y))) ∂gaussianStepLaw m f x) -
        (∫ y, leftRestrict (fderiv ℝ f (x,y)) ∂gaussianStepLaw m f x).smulRight
          (∫ y, leftRestrict (fderiv ℝ f (x,y)) ∂gaussianStepLaw m f x)) := by
  by_cases hm : m = 0
  · subst m
    rw [gaussianStepLaw_zero]
    convert! fderiv_fderiv_gaussianStep_zero hf x using 1
    all_goals try with_reducible_and_instances rfl
    ext u v
    simp
  obtain ⟨hfd,C,D,hC,hD,hb,hbb⟩ := hf
  have hf : BoundedDerivs f := ⟨hfd,C,D,hC,hD,hb,hbb⟩
  let X : ℝ → E →L[ℝ] ℝ := fun y => leftRestrict (fderiv ℝ f (x,y))
  let Y : ℝ → E →L[ℝ] E →L[ℝ] ℝ := fun y =>
    secondLeftRestrict (fderiv ℝ (fderiv ℝ f) (x,y))
  have hX : Continuous X := leftRestrict.continuous.comp
    ((hfd.fderiv_right (m := 1) (by norm_num)).continuous.comp
      (continuous_const.prodMk continuous_id))
  have hY : Continuous Y := secondLeftRestrict.continuous.comp
    ((hfd.fderiv_right (m := 1) (by norm_num) |>.fderiv_right (m := 0) (by norm_num)).continuous.comp
      (continuous_const.prodMk continuous_id))
  have bX (y : ℝ) : ‖X y‖ ≤ C := (leftRestrict_apply_bound _).trans (hb _)
  have bY (y : ℝ) : ‖Y y‖ ≤ D := (secondLeftRestrict_apply_bound _).trans (hbb _)
  have hXX : Continuous (fun y => (X y).smulRight (X y)) :=
    ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)).continuous.comp hX).clm_apply hX
  have bXX (y : ℝ) : ‖(X y).smulRight (X y)‖ ≤ C*C := by
    rw [ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul (bX y) (bX y) (norm_nonneg _) hC
  have iX := integrable_exp_smul_of_bounded hf m x X hX bX
  have iY := integrable_exp_smul_of_bounded hf m x Y hY bY
  have iXX := integrable_exp_smul_of_bounded hf m x (fun y => (X y).smulRight (X y)) hXX bXX
  let A := ∫ y, Real.exp (m*f (x,y)) • X y ∂gaussianReal 0 1
  let B := ∫ y, Real.exp (m*f (x,y)) • Y y ∂gaussianReal 0 1
  let C₂ := ∫ y, Real.exp (m*f (x,y)) • (X y).smulRight (X y) ∂gaussianReal 0 1
  have he₁ (y : ℝ) : leftRestrict
      (fderiv ℝ (fun z => Real.exp (m*f z)) (x,y)) =
      m • (Real.exp (m*f (x,y)) • X y) := by
    rw [((hfd.differentiable (by norm_num) (x,y)).hasFDerivAt.const_mul m).exp.fderiv]
    ext u
    simp only [X,leftRestrict,ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.flip_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply,smul_apply,smul_eq_mul]
    ring
  have he₂ (y : ℝ) : secondLeftRestrict
      (fderiv ℝ (fderiv ℝ (fun z => Real.exp (m*f z))) (x,y)) =
      m • (Real.exp (m*f (x,y)) • Y y) +
      m^2 • (Real.exp (m*f (x,y)) • (X y).smulRight (X y)) := by
    rw [fderiv_fderiv_exp _ (contDiff_const.mul hfd),fderiv_fderiv_const_mul f hfd,
      ((hfd.differentiable (by norm_num) (x,y)).hasFDerivAt.const_mul m).fderiv]
    ext u v
    simp only [X,Y,secondLeftRestrict,leftRestrict,ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.flip_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply,add_apply,
      ContinuousLinearMap.smulRight_apply,smul_apply,smul_eq_mul]
    ring
  rw [fderiv_fderiv_gaussianStep_nonzero hf hm]
  simp_rw [he₁,he₂]
  erw [integral_add (iY.smul m) (iXX.smul (m^2))]
  simp only [Pi.smul_apply]
  erw [iY.integral_smul m, iXX.integral_smul (m^2), iX.integral_smul m]
  simp_rw [gaussianStepLaw_integral_inv_smul]
  change m⁻¹ • ((_ : ℝ) • (m • B + m^2 • C₂) +
    ((_ : ℝ) • (m • A)).smulRight (m • A)) =
    (_ : ℝ) • B + m • ((_ : ℝ) • C₂ - ((_ : ℝ) • A).smulRight ((_ : ℝ) • A))
  ext u v
  simp only [add_apply,sub_apply,
    ContinuousLinearMap.smulRight_apply,smul_apply,smul_eq_mul]
  have hp := (integral_exp_pos (hf.exp_integrable m x)).ne'
  field_simp [hm,hp]
  ring

end CovarianceStep
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

def gaussianAverage (m : ℝ) (f : E × ℝ → ℝ) (g : E × ℝ → F) (x : E) : F :=
  ∫ y, g (x,y) ∂gaussianStepLaw m f x

omit [NormedSpace ℝ F] in
theorem integrable_gaussianStep_of_bounded {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (m : ℝ) (x : E) {g : ℝ → F} (hg : Continuous g) {C : ℝ}
    (hb : ∀ y, ‖g y‖ ≤ C) : Integrable g (gaussianStepLaw m f x) := by
  let := gaussianStepLaw_probability hf m x
  exact Integrable.of_bound hg.aestronglyMeasurable C (ae_of_all _ hb)

theorem gaussianAverage_norm_le {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (m : ℝ) {g : E × ℝ → F} {C : ℝ}
    (hb : ∀ z, ‖g z‖ ≤ C) (x : E) : ‖gaussianAverage m f g x‖ ≤ C := by
  let := gaussianStepLaw_probability hf m x
  simpa only [gaussianAverage,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ := gaussianStepLaw m f x)
      (ae_of_all _ (fun y => hb (x,y)))

theorem prefixGradient_data {f : E × ℝ → ℝ} (hf : BoundedDerivs f) (u : E) :
    Continuous (prefixGradient f u) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖prefixGradient f u z‖ ≤ C := by
  obtain ⟨hc,C,D,hC,hD,hb,hbb⟩ := hf
  refine ⟨(hc.continuous_fderiv (by norm_num)).clm_apply continuous_const,
    C*‖(u,(0:ℝ))‖,mul_nonneg hC (norm_nonneg _),fun z => ?_⟩
  exact ((fderiv ℝ f z).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (hb z) (norm_nonneg _))

theorem prefixHessian_data {f : E × ℝ → ℝ} (hf : BoundedDerivs f) (u v : E) :
    Continuous (prefixHessian f u v) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖prefixHessian f u v z‖ ≤ C := by
  obtain ⟨hc,C,D,hC,hD,hb,hbb⟩ := hf
  refine ⟨((hc.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).clm_apply
    continuous_const |>.clm_apply continuous_const,
    D*‖(u,(0:ℝ))‖*‖(v,(0:ℝ))‖,by positivity,fun z => ?_⟩
  exact ((fderiv ℝ (fderiv ℝ f) z (u,0)).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (((fderiv ℝ (fderiv ℝ f) z).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hbb z) (norm_nonneg _))) (norm_nonneg _))

theorem fderiv_gaussianStep_apply {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (m : ℝ) (x u : E) :
    fderiv ℝ (gaussianStep m f) x u = gaussianAverage m f (prefixGradient f u) x := by
  rw [fderiv_gaussianStep hf]
  have hc : Continuous (fun y : ℝ => leftRestrict (fderiv ℝ f (x,y))) := leftRestrict.continuous.comp
    (hf.1.continuous_fderiv (by norm_num) |>.comp (continuous_const.prodMk continuous_id))
  obtain ⟨hcd,C,D,hC,hD,hb,hbb⟩ := hf
  have hi := integrable_gaussianStep_of_bounded (show BoundedDerivs f from
    ⟨hcd,C,D,hC,hD,hb,hbb⟩) m x hc
    (fun y => (leftRestrict_apply_bound (fderiv ℝ f (x,y))).trans (hb (x,y)))
  rw [ContinuousLinearMap.integral_apply hi]
  rfl

theorem fderiv_fderiv_gaussianStep_apply {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (m : ℝ) (x u v : E) :
    fderiv ℝ (fderiv ℝ (gaussianStep m f)) x u v =
      gaussianAverage m f (prefixHessian f u v) x + m*(
        gaussianAverage m f (fun z => prefixGradient f u z*prefixGradient f v z) x -
        gaussianAverage m f (prefixGradient f u) x*gaussianAverage m f (prefixGradient f v) x) := by
  let X : ℝ → E →L[ℝ] ℝ := fun y => leftRestrict (fderiv ℝ f (x,y))
  let Y : ℝ → E →L[ℝ] E →L[ℝ] ℝ := fun y => secondLeftRestrict (fderiv ℝ (fderiv ℝ f) (x,y))
  obtain ⟨hc,C,D,hC,hD,hb,hbb⟩ := hf
  have hf : BoundedDerivs f := ⟨hc,C,D,hC,hD,hb,hbb⟩
  have hX : Continuous X := leftRestrict.continuous.comp
    (hc.continuous_fderiv (by norm_num) |>.comp (continuous_const.prodMk continuous_id))
  have hY : Continuous Y := secondLeftRestrict.continuous.comp
    ((hc.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num) |>.comp
      (continuous_const.prodMk continuous_id))
  have bX (y : ℝ) : ‖X y‖ ≤ C := (leftRestrict_apply_bound _).trans (hb _)
  have bY (y : ℝ) : ‖Y y‖ ≤ D := (secondLeftRestrict_apply_bound _).trans (hbb _)
  have hXX : Continuous (fun y => (X y).smulRight (X y)) :=
    ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)).continuous.comp hX).clm_apply hX
  have bXX (y : ℝ) : ‖(X y).smulRight (X y)‖ ≤ C*C := by
    rw [ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul (bX y) (bX y) (norm_nonneg _) hC
  have iX := integrable_gaussianStep_of_bounded hf m x hX bX
  have iY := integrable_gaussianStep_of_bounded (F := E →L[ℝ] E →L[ℝ] ℝ) hf m x hY bY
  have iXX := integrable_gaussianStep_of_bounded (F := E →L[ℝ] E →L[ℝ] ℝ) hf m x hXX bXX
  rw [fderiv_fderiv_gaussianStep hf]
  change (∫ y, Y y ∂gaussianStepLaw m f x) u v +
    m*((∫ y, (X y).smulRight (X y) ∂gaussianStepLaw m f x) u v -
      (∫ y, X y ∂gaussianStepLaw m f x) u*(∫ y, X y ∂gaussianStepLaw m f x) v) = _
  rw [ContinuousLinearMap.integral_apply iY,
    ContinuousLinearMap.integral_apply (iY.apply_continuousLinearMap u),
    ContinuousLinearMap.integral_apply iXX,
    ContinuousLinearMap.integral_apply (iXX.apply_continuousLinearMap u),
    ContinuousLinearMap.integral_apply iX,ContinuousLinearMap.integral_apply iX]
  rfl

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
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_ParameterAverage
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
section ParameterAverage
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ParamSmooth.gaussianAverage {f g : P × (E × ℝ) → ℝ}
    (hf : ParamRegular f) (hg : ParamSmooth g) (m : ℝ) :
    ParamSmooth (SK.Analytic.gaussianAverage m
      (fun z : (P × E) × ℝ => f (z.1.1,(z.1.2,z.2)))
      (fun z : (P × E) × ℝ => g (z.1.1,(z.1.2,z.2)))) := by
  have hZ := (((hf.const_mul m).log_gaussian_exp).const_mul (-1)).expSmooth
  have hN := ((hf.const_mul m).expSmooth.mul hg).gaussian_integral
  have he : SK.Analytic.gaussianAverage m
      (fun z : (P × E) × ℝ => f (z.1.1,(z.1.2,z.2)))
      (fun z : (P × E) × ℝ => g (z.1.1,(z.1.2,z.2))) = fun z : P × E =>
      Real.exp (-1*Real.log (∫ y, Real.exp (m*f (z.1,(z.2,y))) ∂gaussianReal 0 1))*
      (∫ y, Real.exp (m*f (z.1,(z.2,y)))*g (z.1,(z.2,y)) ∂gaussianReal 0 1) := by
    funext z
    rw [neg_one_mul,Real.exp_neg,Real.exp_log (hf.exp_gaussian_pos m z)]
    exact gaussianStepLaw_integral_inv_smul m _ z _
  rw [he]
  exact hZ.mul hN
end ParameterAverage
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_ParameterFieldMap
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
section ParameterFieldMap
variable {P E D : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem ParamSmooth.fieldComp {f : P × E → ℝ} (hf : ParamSmooth f) (L : D →L[ℝ] E) :
    ParamSmooth (fun z : P × D => f (z.1,L z.2)) := by
  let A : P × D →L[ℝ] P × E := (ContinuousLinearMap.id ℝ P).prodMap L
  exact ⟨hf.1.comp A.contDiff,hf.2.1.fieldComp L,
    param_fderiv_compCLM_growth f A id (hf.1.differentiable (by norm_num))
      (hf.2.2.1.fieldComp L),
    param_second_compCLM_growth f A id hf.1 (hf.2.2.2.fieldComp L)⟩

end ParameterFieldMap
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_FiniteCoverage
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

def finiteOverlapMass {n : ℕ} (ν : Config n → ℝ) (S : Finset (Config n)) (q : ℝ) : ℝ :=
  ∑ x ∈ S, ∑ y ∈ S, if q ≤ |overlap x y| then ν x*ν y else 0

end SK.Analytic

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

@[simp]
theorem coordinateProjection_coordinateAxis (n : ℕ) (i j : Fin n) :
    coordinateProjection n i (coordinateAxis n j) = if i=j then 1 else 0 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun i => ?_) i
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simp [coordinateProjection,coordinateAxis]
      · simp [coordinateProjection,coordinateAxis,(Fin.castSucc_ne_last j).symm]
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simp [coordinateProjection,coordinateAxis]
      · simpa [coordinateProjection,coordinateAxis] using ih i j

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
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_CascadeRecursion
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

instance cascadeNormedGroup (E : Type) [NormedAddCommGroup E] :
    (n : ℕ) → NormedAddCommGroup (CascadeSpace E n)
  | 0 => inferInstanceAs (NormedAddCommGroup E)
  | n+1 => letI := cascadeNormedGroup E n
    inferInstanceAs (NormedAddCommGroup (CascadeSpace E n × ℝ))

instance cascadeNormedSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (n : ℕ) → NormedSpace ℝ (CascadeSpace E n)
  | 0 => inferInstanceAs (NormedSpace ℝ E)
  | n+1 => letI := cascadeNormedSpace E n
    inferInstanceAs (NormedSpace ℝ (CascadeSpace E n × ℝ))

section Cascade
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def cascadeLift : (n : ℕ) → E → CascadeSpace E n
  | 0,u => u
  | n+1,u => (cascadeLift n u,0)

def cascadePressure : (n : ℕ) → (Fin n → ℝ) → (CascadeSpace E n → ℝ) → E → ℝ
  | 0,_,f => f
  | n+1,m,f => cascadePressure n (fun i => m i.castSucc) (gaussianStep (m (Fin.last n)) f)

def cascadeMoment : (n : ℕ) → (Fin n → ℝ) → (CascadeSpace E n → ℝ) →
    (CascadeSpace E n → ℝ) → E → ℝ
  | 0,_,_,g => g
  | n+1,m,f,g => cascadeMoment n (fun i => m i.castSucc) (gaussianStep (m (Fin.last n)) f)
      (gaussianAverage (m (Fin.last n)) f g)

end Cascade
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
attribute [-instance] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def TailZero : (n : ℕ) → Fin (n+1) → ParameterSpace n → Prop
  | 0,_,_ => True
  | n+1,j,z => Fin.lastCases True (fun i => z.2 = 0 ∧ TailZero n i z.1) j

def PrefixZero : (n : ℕ) → Fin (n+1) → ParameterSpace n → Prop
  | 0,_,z => z = 0
  | n+1,j,z => Fin.lastCases (z = 0) (fun i => PrefixZero n i z.1) j

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

def hierarchyPathLaw (n : ℕ) (m : Fin n → ℝ) (f : ParameterSpace n → ℝ) (x : ℝ) :
    Measure (ParameterSpace n) := (fiberGaussian n x).withDensity
      (fun z => ENNReal.ofReal (hierarchyPathWeight n m f z))

def hierarchyAverage : (n : ℕ) → (Fin n → ℝ) → (ParameterSpace n → ℝ) →
    (ParameterSpace n → ℝ) → ℝ → ℝ
  | 0,_,_,g => g
  | n+1,m,f,g => hierarchyAverage n (fun i => m i.castSucc) (gaussianStep (m (Fin.last n)) f)
      (gaussianAverage (m (Fin.last n)) f g)

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

def hierarchyMomentLevel : (n : ℕ) → (Fin n → ℝ) → (ParameterSpace n → ℝ) →
    (ParameterSpace n → ℝ) → Fin (n+1) → ParameterSpace n → ℝ
  | 0,_,_,g,_ => g
  | n+1,m,f,g,j => Fin.lastCases g (fun i z => hierarchyMomentLevel n
      (fun i => m i.castSucc) (gaussianStep (m (Fin.last n)) f)
      (gaussianAverage (m (Fin.last n)) f g) i z.1) j

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
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def hierarchyPressure : (n : ℕ) → (Fin n → ℝ) → (ParameterSpace n → ℝ) → ℝ → ℝ
  | 0,_,f => f
  | n+1,m,f => hierarchyPressure n (fun i => m i.castSucc)
      (gaussianStep (m (Fin.last n)) f)

theorem hierarchyPressure_boundedDerivs (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) :
    BoundedDerivs (hierarchyPressure n m f) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact ih _ _ (hf.gaussianStep _)

end SK.Analytic
namespace SK.Analytic
attribute [local instance 1900] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def parameterAppend : (a b : ℕ) → CascadeSpace (ParameterSpace a) b ≃L[ℝ] ParameterSpace (a+b)
  | a,0 => ContinuousLinearEquiv.refl ℝ (ParameterSpace a)
  | a,b+1 => (parameterAppend a b).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)

@[simp] theorem parameterAppend_zero (a : ℕ) (x : ParameterSpace a) : parameterAppend a 0 x = x := rfl
@[simp] theorem parameterAppend_succ (a b : ℕ) (x : CascadeSpace (ParameterSpace a) b) (y : ℝ) :
    parameterAppend a (b+1) (x,y) = (parameterAppend a b x,y) := rfl

section CascadeRoot
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def cascadeRoot : (b : ℕ) → CascadeSpace E b →L[ℝ] E
  | 0 => ContinuousLinearMap.id ℝ E
  | b+1 => (cascadeRoot b).comp (ContinuousLinearMap.fst ℝ (CascadeSpace E b) ℝ)
end CascadeRoot

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianStepAlgebra
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
section Generic
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem gaussianStep_add_prefix {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (c : E → ℝ) (m : ℝ) :
    gaussianStep m (fun z => f z+c z.1) = fun x => gaussianStep m f x+c x := by
  funext x
  by_cases hm : m=0
  · subst m
    simp only [gaussianStep,ite_true]
    rw [integral_add (hf.hasExpGrowth.integrable_gaussian_section hf.1.continuous x)
      (integrable_const _)]
    simp
  · simp only [gaussianStep,ite_eq_right hm,positiveGaussianLogStep,mul_add,Real.exp_add]
    rw [integral_mul_const,Real.log_mul (integral_exp_pos (hf.exp_integrable m x)).ne'
      (Real.exp_ne_zero _),Real.log_exp,add_div,mul_div_cancel_left₀ _ hm]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in

theorem gaussianStep_prefix (c : E → ℝ) (m : ℝ) :
    gaussianStep m (fun z : E × ℝ => c z.1) = c := by
  funext x
  by_cases hm : m=0
  · simp [gaussianStep,hm]
  · simp [gaussianStep,hm,positiveGaussianLogStep]

end Generic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

end SK.Analytic

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

theorem hierarchyPenalty_boundedDerivs (n : ℕ) (m : Fin n → ℝ) (u : ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) :
    BoundedDerivs (hierarchyPenalty n m u f) := by
  induction n generalizing u with
  | zero => exact hf.const_mul _
  | succ n ih =>
    let P : ParameterSpace (n+1) →L[ℝ] ParameterSpace n :=
      ContinuousLinearMap.fst ℝ (ParameterSpace n) ℝ
    exact (hf.const_mul _).add ((ih (fun i => m i.castSucc) (m (Fin.last n)) _
      (hf.gaussianStep _)).compCLM P)

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
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ThermalMoments
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
section ThermalMoments
variable {E S : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype S] [Nonempty S]

theorem fderiv_fderiv_affineLogPartition_apply (c : S → ℝ) (L : S → E →L[ℝ] ℝ)
    (x u v : E) : fderiv ℝ (fderiv ℝ (affineLogPartition c L)) x u v =
      affineMoment c L (fun s => L s u*L s v) x -
      affineMoment c L (fun s => L s u) x*affineMoment c L (fun s => L s v) x := by
  classical
  let Z : E → ℝ := fun x => ∑ s, Real.exp (c s+L s x)
  let Z₁ : E → E →L[ℝ] ℝ := fun x => ∑ s, Real.exp (c s+L s x) • L s
  let Z₂ : E → E →L[ℝ] E →L[ℝ] ℝ := fun x =>
    ∑ s, (Real.exp (c s+L s x) • L s).smulRight (L s)
  have hd (s : S) (x : E) : HasFDerivAt (fun x => c s+L s x) (L s) x := by
    simpa only [zero_add] using (hasFDerivAt_const (c s) x).fun_add (L s).hasFDerivAt
  have hz₁ (x : E) : HasFDerivAt Z (Z₁ x) x :=
    HasFDerivAt.fun_sum (fun s _ => (hd s x).exp)
  have hz₂ (x : E) : HasFDerivAt Z₁ (Z₂ x) x :=
    HasFDerivAt.fun_sum (fun s _ => (hd s x).exp.smul_const (L s))
  have he : fderiv ℝ Z = Z₁ := funext (fun x => (hz₁ x).fderiv)
  have he₂ : fderiv ℝ (fderiv ℝ Z) = Z₂ := by
    rw [he]
    exact funext (fun x => (hz₂ x).fderiv)
  have hc : ContDiff ℝ 2 Z := by
    apply ContDiff.sum
    intro s _
    exact (contDiff_const.add (L s).contDiff).exp
  have hp (x : E) : Z x ≠ 0 := (affinePartition_pos c L x).ne'
  change fderiv ℝ (fderiv ℝ (fun x => Real.log (Z x))) x u v = _
  rw [fderiv_fderiv_log Z hc hp,he₂,he]
  simp only [Z₁,Z₂,smul_apply,smul_eq_mul,sum_apply,add_apply,ContinuousLinearMap.smulRight_apply,
    affineMoment,affineGibbs]
  have ha (g : S → ℝ) : (∑ s, Real.exp (c s+L s x)/(Z x)*g s) =
      (Z x)⁻¹*∑ s, Real.exp (c s+L s x)*g s := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  simp_rw [show (∑ t, Real.exp (c t+L t x)) = Z x from rfl,ha]
  rw [Finset.mul_sum]
  have hs : (∑ s, (Z x)⁻¹*(Real.exp (c s+L s x)*L s u*L s v)) =
      (Z x)⁻¹*∑ s, Real.exp (c s+L s x)*(L s u*L s v) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [hs]
  field_simp [hp x]
  ring

end ThermalMoments
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

section SpinMeans
variable {S : Type} [Fintype S] [Nonempty S]

def hierarchySpinMean (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (c : S → ℝ) (j : Fin (n+1)) : ParameterSpace n → ℝ :=
  hierarchyMomentLevel n m (affineLogPartition (fun _ => 0) U) (affineMoment (fun _ => 0) U c) j

end SpinMeans
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyPrefix
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

@[simp] theorem TailZero.zero (n : ℕ) (j : Fin (n+1)) : TailZero n j 0 := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [TailZero,Fin.lastCases_last]
    · simp only [TailZero,Fin.lastCases_castSucc]
      exact ⟨rfl,ih j⟩

@[simp] theorem PrefixZero.zero (n : ℕ) (j : Fin (n+1)) : PrefixZero n j 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [PrefixZero,Fin.lastCases_last]
    · simpa only [PrefixZero,Fin.lastCases_castSucc,Prod.fst_zero] using ih j

@[simp] theorem coordinateLinear_coordinateAxis (n : ℕ) (a : Fin n → ℝ) (i : Fin n) :
    coordinateLinear n a (coordinateAxis n i) = a i := by
  simp [coordinateLinear_apply,coordinateProjection_coordinateAxis]

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

def hierarchyMeanSquare {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ) (j : Fin (n+1)) (z : ParameterSpace n) : ℝ :=
  normalizedSquare (fun i => hierarchySpinMean n m U (c i) j z)

end MeanSquare

end SK.Analytic
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section MeanTower
variable {S : Type} [Fintype S] [Nonempty S]

def hierarchyMeanOverlap {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ) (j : Fin (n+1)) : ℝ :=
  ∫ z, hierarchyMeanSquare n m U c j z ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0

end MeanTower
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_SpinMonomials
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
namespace SK
open Analytic

def spinExponent {N : ℕ} (d : ℕ) (a : Fin d → ℝ) (I : Fin d → Finset (Fin N))
    (s : Config N) : ParameterSpace d →L[ℝ] ℝ :=
  coordinateLinear d (fun j => a j*spinMonomial s (I j))

end SK

end
end
end
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

def blockExponent {D N k : ℕ} (I : Fin D → Finset (Fin N)) (a : Fin D → ℝ)
    (v : Fin (k+1) → ℝ) := spinExponent (blockDimension D N k) (blockCoefficients a v) (blockInteraction I)

def blockFieldEnergy {D N k : ℕ} (v : Fin (k+1) → ℝ)
    (sz : Config N × ParameterSpace (blockDimension D N k)) : ℝ :=
  (∑ b : Fin (k+1), ∑ i : Fin N,
    v b*coordinateProjection (blockDimension D N k) (fieldIndex D N k b i) sz.2*spin (sz.1 i))/(N : ℝ)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_CascadeProbability
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
section CascadeProbability
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {S : Type} [Fintype S] [Nonempty S]

def cascadeSpinWeight (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (L : S → CascadeSpace E n →L[ℝ] ℝ) (x : E) (s : S) : ℝ :=
  cascadeMoment n m (affineLogPartition c L) (fun z => affineGibbs c L z s) x

end CascadeProbability
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

def cascadeMap : (n : ℕ) → (E → F) → CascadeSpace E n → CascadeSpace F n
  | 0,A => A
  | n+1,A => fun z => (cascadeMap n A z.1,z.2)

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

def cascadeMapCLM : (n : ℕ) → (E →L[ℝ] F) → CascadeSpace E n →L[ℝ] CascadeSpace F n
  | 0,A => A
  | n+1,A => (cascadeMapCLM n A).prodMap (ContinuousLinearMap.id ℝ ℝ)

end CascadeMap
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianSpinTrace
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

noncomputable section
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped MatrixOrder BigOperators
noncomputable section
open scoped BigOperators MatrixOrder
open MeasureTheory ProbabilityTheory Matrix
namespace SK.Analytic
open Matrix
open scoped MatrixOrder
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section CascadeFieldCurvature
variable {E S : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype S] [Nonempty S]

def cascadeLiftCLM : (n : ℕ) → E →L[ℝ] CascadeSpace E n
  | 0 => ContinuousLinearMap.id ℝ E
  | n+1 => (cascadeLiftCLM n).prod 0

@[simp]
theorem cascadeLiftCLM_apply (n : ℕ) (u : E) : cascadeLiftCLM (E := E) n u = cascadeLift n u := by
  induction n with
  | zero => rfl
  | succ n ih => change (cascadeLiftCLM (E := E) n u,0) = (cascadeLift n u,0); rw [ih]

end CascadeFieldCurvature

end SK.Analytic

end
end
end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyBlocks
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

def parameterBlocks : (a b c : ℕ) →
    CascadeSpace (CascadeSpace (ParameterSpace a) b) c ≃L[ℝ] ParameterSpace (a+(b+c))
  | a,b,0 => parameterAppend a b
  | a,b,c+1 => (parameterBlocks a b c).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)

@[simp] theorem parameterBlocks_succ (a b c : ℕ)
    (z : CascadeSpace (CascadeSpace (ParameterSpace a) b) c) (y : ℝ) :
    parameterBlocks a b (c+1) (z,y) = (parameterBlocks a b c z,y) := rfl

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_BlockAdaptiveOverlap
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

def blockAdaptiveOverlap {D N k : ℕ} (I : Fin D → Finset (Fin N)) (a : Fin D → ℝ)
    (β : ℝ) (p : ℝ × (Fin (k+1) → ℝ)) (j : Fin (k+1)) : ℝ :=
  hierarchyMeanOverlap (blockDimension D N k) (blockMass D N k)
    (blockExponent I (fun i => p.1*a i) (fun b => β*p.2 b))
    (fun i s => spin (s i)) (blockLevel D N k j)

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

def scalarStep (m v : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  gaussianStep m (fun z : ℝ × ℝ => f (z.1+v*z.2))

def scalarHierarchy : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ) → (ℝ → ℝ) → ℝ → ℝ
  | 0,_,_,f => f
  | n+1,m,v,f => scalarHierarchy n (fun i => m i.castSucc) (fun i => v i.castSucc)
      (scalarStep (m (Fin.last n)) (v (Fin.last n)) f)

@[simp] theorem scalarStep_zero (m : ℝ) (f : ℝ → ℝ) : scalarStep m 0 f = f := by
  simp only [scalarStep,zero_mul,add_zero]
  exact gaussianStep_prefix f m

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarCurvature
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
section OneStep
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem gaussianStep_spin_curvature {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) (u x : E)
    (hH : ∀ y, 0 < prefixHessian f u u (x,y) ∧
      prefixHessian f u u (x,y) ≤ 1-(prefixGradient f u (x,y))^2) :
    0 < fderiv ℝ (fderiv ℝ (gaussianStep m f)) x u u ∧
      fderiv ℝ (fderiv ℝ (gaussianStep m f)) x u u ≤
        1-(fderiv ℝ (gaussianStep m f) x u)^2 := by
  let μ := gaussianStepLaw m f x
  let := gaussianStepLaw_probability hf m x
  obtain ⟨hcG,B,_hB,hbG⟩ := prefixGradient_data hf u
  obtain ⟨hcH,C,_hC,hbH⟩ := prefixHessian_data hf u u
  have hcm : Continuous (fun y : ℝ => prefixGradient f u (x,y)) := hcG.comp (continuous_const.prodMk (continuous_id : Continuous (fun y : ℝ => y)))
  have hmem : MemLp (fun y => prefixGradient f u (x,y)) 2 μ :=
    MemLp.of_bound hcm.aestronglyMeasurable B (ae_of_all _ (fun y => hbG (x,y)))
  have iH : Integrable (fun y => prefixHessian f u u (x,y)) μ :=
    integrable_gaussianStep_of_bounded hf m x
      (hcH.comp (continuous_const.prodMk continuous_id)) (fun y => hbH (x,y))
  have hv := variance_nonneg (fun y => prefixGradient f u (x,y)) μ
  rw [variance_eq_sub hmem] at hv
  have hpos : 0 < ∫ y, prefixHessian f u u (x,y) ∂μ := by
    rw [integral_pos_iff_support_of_nonneg (fun y => (hH y).1.le) iH]
    have he : Function.support (fun y => prefixHessian f u u (x,y)) = Set.univ := by
      ext y
      simp only [Function.mem_support,Set.mem_univ]
      exact iff_true_intro (hH y).1.ne'
    rw [he,measure_univ]
    exact zero_lt_one
  have hupper := integral_mono iH ((integrable_const (1:ℝ)).sub hmem.integrable_sq)
    (fun y => (hH y).2)
  change (∫ y, prefixHessian f u u (x,y) ∂μ) ≤
    ∫ y, 1-(prefixGradient f u (x,y))^2 ∂μ at hupper
  rw [integral_sub (integrable_const _) hmem.integrable_sq,integral_const] at hupper
  simp only [Measure.real,measure_univ,ENNReal.toReal_one,smul_eq_mul,one_mul] at hupper
  rw [fderiv_fderiv_gaussianStep_apply hf,fderiv_gaussianStep_apply hf]
  simp only [gaussianAverage,pow_two,Pi.mul_apply] at hv hupper ⊢
  dsimp only [μ] at hv hupper hpos
  constructor
  · nlinarith [mul_nonneg hm.1 hv]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hm.2) hv]

theorem affineLogPartition_bool_curvature (L : E →L[ℝ] ℝ) (z u : E) (hL : L u = 1) :
    let f := affineLogPartition (fun _ : Bool => 0) (fun b => spin b • L)
    0 < fderiv ℝ (fderiv ℝ f) z u u ∧
      fderiv ℝ (fderiv ℝ f) z u u = 1-(fderiv ℝ f z u)^2 := by
  dsimp only
  rw [fderiv_fderiv_affineLogPartition_apply,fderiv_affineLogPartition_apply]
  have hpos₀ := affineGibbs_pos (fun _ : Bool => 0) (fun b => spin b • L) z false
  have hpos₁ := affineGibbs_pos (fun _ : Bool => 0) (fun b => spin b • L) z true
  have hsum := affineGibbs_sum (fun _ : Bool => 0) (fun b => spin b • L) z
  simp only [Fintype.sum_bool] at hsum
  simp only [spin] at hpos₀ hpos₁ hsum
  simp only [affineMoment,Fintype.sum_bool,smul_apply,smul_eq_mul,hL,mul_one,
    spin,Bool.false_eq_true,ite_false,ite_true,neg_one_mul]
  constructor <;> nlinarith [mul_pos hpos₀ hpos₁]
end OneStep
attribute [local instance 1900] cascadeNormedGroup cascadeNormedSpace
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
section Terminal
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem affineLogPartition_bool (L : E →L[ℝ] ℝ) (z : E) :
    affineLogPartition (fun _ : Bool => 0) (fun b => spin b • L) z =
      Real.log (2*Real.cosh (L z)) := by
  simp only [affineLogPartition,zero_add,smul_apply,smul_eq_mul,
    Fintype.sum_bool,spin,Bool.false_eq_true,ite_false,ite_true,one_mul,neg_one_mul,Real.cosh_eq]
  congr 1
  ring
end Terminal

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

def scalarSpinField (n : ℕ) (v : Fin n → ℝ) : ParameterSpace n →L[ℝ] ℝ :=
  parameter n+coordinateLinear n v

theorem scalarSpinTerminal_affine (n : ℕ) (v : Fin n → ℝ) :
    (fun z => scalarSpinTerminal (parameter n z+∑ j, v j*coordinateProjection n j z)) =
      affineLogPartition (fun _ : Bool => 0) (fun b => spin b • scalarSpinField n v) := by
  funext z
  rw [affineLogPartition_bool]
  simp only [scalarSpinTerminal,scalarSpinField,add_apply,coordinateLinear_apply]

theorem hierarchy_spin_curvature (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f)
    (hm : ∀ i, m i ∈ Set.Icc 0 1)
    (hH : ∀ z, 0 < fderiv ℝ (fderiv ℝ f) z (parameterAxis n) (parameterAxis n) ∧
      fderiv ℝ (fderiv ℝ f) z (parameterAxis n) (parameterAxis n) ≤
        1-(fderiv ℝ f z (parameterAxis n))^2) (x : ℝ) :
    0 < fderiv ℝ (fderiv ℝ (hierarchyPressure n m f)) x 1 1 ∧
      fderiv ℝ (fderiv ℝ (hierarchyPressure n m f)) x 1 1 ≤
        1-(fderiv ℝ (hierarchyPressure n m f) x 1)^2 := by
  induction n with
  | zero => exact hH x
  | succ n ih =>
    apply ih (fun i => m i.castSucc) _ (hf.gaussianStep _) (fun i => hm i.castSucc)
    intro z
    apply gaussianStep_spin_curvature hf (hm (Fin.last n)) (parameterAxis n) z
    intro y
    exact hH (z,y)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_WeightedConcentration
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
namespace SK.Analytic.Weighted

class Weights (n : ℕ) where
  weight : Config n → ℝ
  nonneg : ∀ x, 0 ≤ weight x
  sum_one : ∑ x, weight x = 1

def partition {n : ℕ} [Weights n] (β : ℝ) (J : Disorder n) : ℝ :=
  ∑ x : Config n, Weights.weight x * Real.exp (β * hamiltonian J x)

def gibbs {n : ℕ} [Weights n] (β : ℝ) (J : Disorder n) (x : Config n) : ℝ :=
  Weights.weight x * Real.exp (β * hamiltonian J x) / partition β J

def directionalEnergy {n : ℕ} [Weights n] (β : ℝ) (J K : Disorder n) : ℝ :=
  β * ∑ x : Config n, gibbs β J x * hamiltonian K x

def logPartition {n : ℕ} [Weights n] (β : ℝ) (J : Disorder n) : ℝ := Real.log (partition β J)

def rotationIntegrand {n : ℕ} [Weights n] (β θ ℓ : ℝ) (s : ℝ) (p : Disorder n × Disorder n) : ℝ :=
  Real.exp (ℓ * θ * directionalEnergy β (rotateDisorder (θ * s) p).1
    (rotateDisorder (θ * s) p).2)

@[simp] theorem rotateDisorder_pi_div_two_fst {n : ℕ} [Weights n] (p : Disorder n × Disorder n) :
    (rotateDisorder (Real.pi / 2) p).1 = p.2 := by
  funext e
  simp [rotateDisorder, mixDisorder]

end SK.Analytic.Weighted

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_UniformCoverage
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

def coveragePairBad (n : ℕ) (β m r q : ℝ) : Set (Disorder n) :=
  {J | ∃ S : Finset (Config n), m ≤ finiteMass (gibbs β J) S ∧
    finiteOverlapMass (gibbs β J) S q < r*(finiteMass (gibbs β J) S)^2}

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_HeatBathEnergy
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

@[simp] theorem coupling_self {n : ℕ} (J : Disorder n) (i : Fin n) : coupling J i i = 0 := by
  simp [coupling]

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_BankCoverage
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

def bankJointIndex {p : ℕ} (K : Fin p → ℕ) (pred : Fin p → Finset (Fin p)) (j : Fin p)
    (T : BankTuple K pred j) : BankPrior pred j ⊕ Fin (K j) → BankIndex K :=
  Sum.elim (fun i => ⟨i.val,T i⟩) (fun a => ⟨j,a⟩)

def bankCell {n p : ℕ} (K : Fin p → ℕ) (pred : Fin p → Finset (Fin p)) (t : ℝ)
    (z : BankIndex K → Config n) (j : Fin p) (T : BankTuple K pred j) (x : Config n) : Prop :=
  ∀ i : BankPrior pred j, |overlap (z ⟨i.val,T i⟩) x|≤3*t

def bankCoverageBad {n p : ℕ} (K : Fin p → ℕ) (pred : Fin p → Finset (Fin p)) (t q : ℝ)
    (z : BankIndex K → Config n) (x : Config n) : Prop :=
  ∃ j : Fin p, ∃ T : BankTuple K pred j, bankCell K pred t z j T x ∧
    ∀ a : Fin (K j), ¬(bankCell K pred t z j T (z ⟨j,a⟩) ∧ q≤|overlap x (z ⟨j,a⟩)|)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_SmoothFamily
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
namespace SK.Analytic.SmoothFamily

def logPartition {n : ℕ} [Model n] := Model.logPartition (n := n)
def gibbs {n : ℕ} [Model n] := Model.gibbs (n := n)

def directionalEnergy {n : ℕ} [Model n] (β : ℝ) (J K : Disorder n) : ℝ :=
  β * ∑ x : Config n, gibbs β J x * hamiltonian K x

def rotationIntegrand {n : ℕ} [Model n] (β θ ℓ : ℝ) (s : ℝ) (p : Disorder n × Disorder n) : ℝ :=
  Real.exp (ℓ * θ * directionalEnergy β (rotateDisorder (θ * s) p).1
    (rotateDisorder (θ * s) p).2)

end SK.Analytic.SmoothFamily

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_ReplicaSampling
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

def orient {n : ℕ} (ε : Bool) (x : Config n) : Config n := if ε then flip x else x

@[simp] theorem orient_orient {n : ℕ} (ε : Bool) (x : Config n) : orient ε (orient ε x)=x := by
  cases ε <;> simp [orient]
@[simp] theorem gibbs_orient {n : ℕ} (β : ℝ) (J : Disorder n) (ε : Bool) (x : Config n) :
    gibbs β J (orient ε x)=gibbs β J x := by cases ε <;> simp [orient]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_BankAvoidance
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

def bankTripleBad {n : ℕ} {I : Type*} (level : I → ℕ) (S : Finset (ReplicaConfig n 3))
    (z : I → Config n) : Prop :=
  ∃ v : I × I × I × (Fin 3 → Bool),
    (level v.1≠level v.2.1 ∧ level v.1≠level v.2.2.1 ∧ level v.2.1≠level v.2.2.1) ∧
    (![orient (v.2.2.2 0) (z v.1),orient (v.2.2.2 1) (z v.2.1),orient (v.2.2.2 2) (z v.2.2.1)] : ReplicaConfig n 3)∈S

def bankVertexBad {n : ℕ} {I : Type*} (level : I → ℕ) (S : Finset (ReplicaConfig n 3))
    (z : I → Config n) (x : Config n) : Prop :=
  ∃ v : I × I × (Fin 3 → Bool) × Equiv.Perm (Fin 3),
    level v.1≠level v.2.1 ∧
    (fun i => orient (v.2.2.1 i) ((![z v.1,z v.2.1,x] : ReplicaConfig n 3) (v.2.2.2 i)))∈S

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_BankCardinality
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

def blockPriorEquiv (p B : ℕ) (j : Fin p) : BankPrior (blockPrior p B) j ≃ Fin (j.val%B) where
  toFun i := ⟨i.val.val-j.val/B*B,by
    have h := (mem_blockPrior p B i.val j).mp i.property
    have hd : j.val%B+j.val/B*B=j.val := by simpa only [Nat.mul_comm] using Nat.mod_add_div j.val B
    omega⟩
  invFun a := ⟨⟨j.val/B*B+a.val,by
    have hd : j.val%B+j.val/B*B=j.val := by simpa only [Nat.mul_comm] using Nat.mod_add_div j.val B
    have h := j.isLt
    omega⟩,by
    apply (mem_blockPrior p B _ j).mpr
    have hd : j.val%B+j.val/B*B=j.val := by simpa only [Nat.mul_comm] using Nat.mod_add_div j.val B
    change j.val/B*B≤j.val/B*B+a.val ∧ j.val/B*B+a.val<j.val
    constructor <;> omega⟩
  left_inv i := by
    apply Subtype.ext
    apply Fin.ext
    have h := (mem_blockPrior p B i.val j).mp i.property
    simp only
    omega
  right_inv a := by
    apply Fin.ext
    simp only
    omega

end SK.Analytic

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

def rootGradient (n : ℕ) (f : ParameterSpace n → ℝ) (z : ParameterSpace n) : ℝ :=
  fderiv ℝ f z (parameterAxis n)

def rootHessian (n : ℕ) (f : ParameterSpace n → ℝ) (z : ParameterSpace n) : ℝ :=
  fderiv ℝ (fderiv ℝ f) z (parameterAxis n) (parameterAxis n)

def RootSpinCurvature (n : ℕ) (f : ParameterSpace n → ℝ) : Prop :=
  ∀ z, 0 < rootHessian n f z ∧ rootHessian n f z ≤ 1-(rootGradient n f z)^2

theorem RootSpinCurvature.bounds {n : ℕ} {f : ParameterSpace n → ℝ}
    (h : RootSpinCurvature n f) (z : ParameterSpace n) :
    |rootGradient n f z| ≤ 1 ∧ |rootHessian n f z| ≤ 1 := by
  have H := h z
  refine ⟨(sq_le_one_iff_abs_le_one _).mp (by linarith),?_⟩
  rw [abs_of_pos H.1]
  linarith [sq_nonneg (rootGradient n f z)]

theorem RootSpinCurvature.gaussianStep {n : ℕ} {f : ParameterSpace (n+1) → ℝ}
    (h : RootSpinCurvature (n+1) f) (hf : BoundedDerivs f) {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) :
    RootSpinCurvature n (gaussianStep m f) := by
  intro z
  exact gaussianStep_spin_curvature hf hm (parameterAxis n) z (fun y => h (z,y))

theorem rootLine_hasDerivAt (n : ℕ) {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f)
    (z : ParameterSpace n) (t : ℝ) :
    HasDerivAt (fun a : ℝ => f (z+a • parameterAxis n))
      (rootGradient n f (z+t • parameterAxis n)) t := by
  have hd : HasDerivAt (fun a : ℝ => z+a • parameterAxis n) (parameterAxis n) t := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id t).smul_const (parameterAxis n)).const_add z
  exact ((hf.1.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t hd)

theorem rootGradientLine_hasDerivAt (n : ℕ) {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f)
    (z : ParameterSpace n) (t : ℝ) :
    HasDerivAt (fun a : ℝ => rootGradient n f (z+a • parameterAxis n))
      (rootHessian n f (z+t • parameterAxis n)) t := by
  have hd : HasDerivAt (fun a : ℝ => z+a • parameterAxis n) (parameterAxis n) t := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id t).smul_const (parameterAxis n)).const_add z
  have h := ((directionalGradient_contDiff f hf.1 (parameterAxis n)).differentiable
      (by norm_num) (z+t • parameterAxis n)).hasFDerivAt.comp_hasDerivAt t hd
  rw [fderiv_directionalGradient f hf.1] at h
  exact h

theorem rootGradient_fst (n : ℕ) {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f)
    (z : ParameterSpace (n+1)) :
    rootGradient (n+1) (fun z : ParameterSpace (n+1) => f z.1) z = rootGradient n f z.1 := by
  let P : ParameterSpace (n+1) →L[ℝ] ParameterSpace n := ContinuousLinearMap.fst ℝ (ParameterSpace n) ℝ
  have hd := (hf.1.differentiable (by norm_num) z.1).hasFDerivAt.comp z P.hasFDerivAt
  unfold rootGradient
  have he : fderiv ℝ (fun z : ParameterSpace (n+1) => f z.1) z =
      (fderiv ℝ f z.1).comp P := hd.fderiv
  rw [he]
  rfl

theorem rootGradient_penalty_succ (n : ℕ) (m : Fin (n+1) → ℝ) (u : ℝ)
    {f : ParameterSpace (n+1) → ℝ} (hf : BoundedDerivs f) (z : ParameterSpace (n+1)) :
    rootGradient (n+1) (hierarchyPenalty (n+1) m u f) z =
      (u-m (Fin.last n))*rootGradient (n+1) f z+
      rootGradient n (hierarchyPenalty n (fun i => m i.castSucc) (m (Fin.last n))
        (gaussianStep (m (Fin.last n)) f)) z.1 := by
  let g := hierarchyPenalty n (fun i => m i.castSucc) (m (Fin.last n)) (gaussianStep (m (Fin.last n)) f)
  have hg : BoundedDerivs g := hierarchyPenalty_boundedDerivs _ _ _ _ (hf.gaussianStep _)
  have hgP := hg.compCLM (ContinuousLinearMap.fst ℝ (ParameterSpace n) ℝ)
  have hd := ((hf.1.differentiable (by norm_num) z).hasFDerivAt.const_mul (u-m (Fin.last n))).add
    (hgP.1.differentiable (by norm_num) z).hasFDerivAt
  change fderiv ℝ (fun z : ParameterSpace (n+1) => (u-m (Fin.last n))*f z+g z.1) z _ = _
  have he : fderiv ℝ (fun z : ParameterSpace (n+1) => (u-m (Fin.last n))*f z+g z.1) z =
      ((u-m (Fin.last n)) • fderiv ℝ f z)+fderiv ℝ (fun z : ParameterSpace (n+1) => g z.1) z := hd.fderiv
  rw [he]
  simp only [add_apply,smul_apply,smul_eq_mul]
  change (u-m (Fin.last n))*rootGradient (n+1) f z+
    rootGradient (n+1) (fun z : ParameterSpace (n+1) => g z.1) z = _
  rw [rootGradient_fst n hg]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_RootHessianIdentity
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

theorem rootGradient_penalty_zero (m : Fin 0 → ℝ) (u : ℝ) {f : ParameterSpace 0 → ℝ}
    (hf : BoundedDerivs f) (x : ℝ) :
    rootGradient 0 (hierarchyPenalty 0 m u f) x=u*rootGradient 0 f x := by
  have hd := (hf.1.differentiable (by norm_num) x).hasFDerivAt.const_mul u
  change fderiv ℝ (fun z : ℝ => u*f z) x 1=u*fderiv ℝ f x 1
  rw [hd.fderiv]
  rfl

def rootResponse (n : ℕ) (m : Fin n → ℝ) (u : ℝ) (f : ParameterSpace n → ℝ)
    (z : ParameterSpace n) : ℝ :=
  rootHessian n f z+u*(rootGradient n f z)^2-
    rootGradient n f z*rootGradient n (hierarchyPenalty n m u f) z

theorem gaussianAverage_rootResponse (n : ℕ) (m : Fin (n+1) → ℝ) (u : ℝ)
    {f : ParameterSpace (n+1) → ℝ} (hf : BoundedDerivs f) (z : ParameterSpace n) :
    gaussianAverage (m (Fin.last n)) f (rootResponse (n+1) m u f) z =
      rootResponse n (fun i => m i.castSucc) (m (Fin.last n))
        (gaussianStep (m (Fin.last n)) f) z := by
  let q := m (Fin.last n)
  let G : ℝ → ℝ := fun y => rootGradient (n+1) f (z,y)
  let H : ℝ → ℝ := fun y => rootHessian (n+1) f (z,y)
  let μ := gaussianStepLaw q f z
  let P := rootGradient n (hierarchyPenalty n (fun i => m i.castSucc) q (gaussianStep q f)) z
  let := gaussianStepLaw_probability hf q z
  obtain ⟨hcG,B,_hB,hbG⟩ := prefixGradient_data hf (parameterAxis n)
  obtain ⟨hcH,C,_hC,hbH⟩ := prefixHessian_data hf (parameterAxis n) (parameterAxis n)
  have hmg : MemLp G 2 μ := MemLp.of_bound
    (hcG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable B
    (ae_of_all _ (fun y => hbG (z,y)))
  have iG : Integrable G μ := hmg.integrable one_le_two
  have iH : Integrable H μ := integrable_gaussianStep_of_bounded hf q z
    (hcH.comp (continuous_const.prodMk continuous_id)) (fun y => hbH (z,y))
  have he (y : ℝ) : rootResponse (n+1) m u f (z,y) = H y+q*(G y)^2-G y*P := by
    rw [rootResponse,rootGradient_penalty_succ n m u hf]
    change H y+u*(G y)^2-G y*((u-q)*G y+P)=_
    ring
  change (∫ y, rootResponse (n+1) m u f (z,y) ∂μ)=_
  simp_rw [he]
  have iHG : Integrable (fun y => H y+q*(G y)^2) μ := iH.add (hmg.integrable_sq.const_mul q)
  rw [integral_sub iHG (iG.mul_const P),
    integral_add iH (hmg.integrable_sq.const_mul q), integral_const_mul, integral_mul_const]
  have hG : rootGradient n (gaussianStep q f) z=∫ y, G y ∂μ :=
    fderiv_gaussianStep_apply hf q z (parameterAxis n)
  have hH : rootHessian n (gaussianStep q f) z=
      (∫ y, H y ∂μ)+q*((∫ y, G y*G y ∂μ)-(∫ y, G y ∂μ)*(∫ y, G y ∂μ)) :=
    fderiv_fderiv_gaussianStep_apply hf q z (parameterAxis n) (parameterAxis n)
  change _=rootHessian n (gaussianStep q f) z+q*(rootGradient n (gaussianStep q f) z)^2-
    rootGradient n (gaussianStep q f) z*P
  rw [hH,hG]
  simp only [pow_two]
  ring

theorem hierarchyPressure_rootHessian (n : ℕ) (m : Fin n → ℝ) (u : ℝ)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (x : ℝ) :
    rootHessian 0 (hierarchyPressure n m f) x=
      hierarchyAverage n m f (rootResponse n m u f) x := by
  induction n generalizing u with
  | zero =>
    change rootHessian 0 f x=rootResponse 0 m u f x
    rw [rootResponse,rootGradient_penalty_zero m u hf]
    ring
  | succ n ih =>
    change rootHessian 0 (hierarchyPressure n (fun i => m i.castSucc) (gaussianStep (m (Fin.last n)) f)) x=
      hierarchyAverage n (fun i => m i.castSucc) (gaussianStep (m (Fin.last n)) f)
        (gaussianAverage (m (Fin.last n)) f (rootResponse (n+1) m u f)) x
    have he : gaussianAverage (m (Fin.last n)) f (rootResponse (n+1) m u f)=
        rootResponse n (fun i => m i.castSucc) (m (Fin.last n)) (gaussianStep (m (Fin.last n)) f) :=
      funext (gaussianAverage_rootResponse n m u hf)
    rw [he]
    exact ih (fun i => m i.castSucc) _ (hf.gaussianStep _)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_RootGeneralCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem rootGradient_gaussianStep (n : ℕ) {f : ParameterSpace (n+1) → ℝ}
    (hf : BoundedDerivs f) (m : ℝ) (z : ParameterSpace n) :
    rootGradient n (gaussianStep m f) z=gaussianAverage m f (rootGradient (n+1) f) z :=
  fderiv_gaussianStep_apply hf m z (parameterAxis n)

theorem rootGradient_gaussianStep_bound (n : ℕ) {f : ParameterSpace (n+1) → ℝ}
    (hf : BoundedDerivs f) (m : ℝ) {B : ℝ} (hB : ∀ z, |rootGradient (n+1) f z| ≤ B)
    (z : ParameterSpace n) : |rootGradient n (gaussianStep m f) z| ≤ B := by
  rw [rootGradient_gaussianStep n hf m z]
  simpa only [Real.norm_eq_abs] using gaussianAverage_norm_le hf m (g := rootGradient (n+1) f) (C := B)
    (fun z => by simpa only [Real.norm_eq_abs] using hB z) z

theorem hierarchyAverage_abs_le (n : ℕ) (m : Fin n → ℝ)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (g : ParameterSpace n → ℝ)
    {B : ℝ} (hB : ∀ z, |g z| ≤ B) (x : ℝ) : |hierarchyAverage n m f g x| ≤ B := by
  induction n with
  | zero => exact hB x
  | succ n ih =>
    apply ih (fun i => m i.castSucc) (hf.gaussianStep _) _
    intro z
    simpa only [Real.norm_eq_abs] using gaussianAverage_norm_le hf (m (Fin.last n)) (g := g) (C := B)
      (fun z => by simpa only [Real.norm_eq_abs] using hB z) z

theorem hierarchyPressure_rootGradient (n : ℕ) (m : Fin n → ℝ)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (x : ℝ) :
    rootGradient 0 (hierarchyPressure n m f) x=
      hierarchyAverage n m f (rootGradient n f) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change rootGradient 0 (hierarchyPressure n (fun i => m i.castSucc)
      (gaussianStep (m (Fin.last n)) f)) x= _
    rw [ih (fun i => m i.castSucc) (hf.gaussianStep _)]
    simp only [hierarchyAverage,funext (rootGradient_gaussianStep n hf (m (Fin.last n)))]

theorem rootGradient_penalty_bound_general (n : ℕ) (m : Fin n → ℝ)
    {u B : ℝ} (hu : 0 ≤ u) (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ u) (hmono : Monotone m)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f)
    (hB : ∀ z, |rootGradient n f z| ≤ B)
    (z : ParameterSpace n) : |rootGradient n (hierarchyPenalty n m u f) z| ≤ u*B := by
  induction n generalizing u with
  | zero =>
    rw [rootGradient_penalty_zero m u hf,abs_mul,abs_of_nonneg hu]
    exact mul_le_mul_of_nonneg_left (hB z) hu
  | succ n ih =>
    let q := m (Fin.last n)
    have hb := ih (fun i => m i.castSucc) (hm (Fin.last n)) (fun i => hm i.castSucc)
      (fun i => hmono (Fin.le_last _))
      (fun _ _ hij => hmono (Fin.castSucc_le_castSucc_iff.mpr hij))
      (hf.gaussianStep q) (rootGradient_gaussianStep_bound n hf q hB) z.1
    rw [rootGradient_penalty_succ n m u hf]
    calc
      _ ≤ |(u-q)*rootGradient (n+1) f z|+
        |rootGradient n (hierarchyPenalty n (fun i => m i.castSucc) q (gaussianStep q f)) z.1| := abs_add_le _ _
      _ ≤ (u-q)*B+q*B := add_le_add (by
        rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr (hmu _))]
        exact mul_le_mul_of_nonneg_left (hB z) (sub_nonneg.mpr (hmu _))) hb
      _ = u*B := by ring

theorem hierarchyPressure_rootHessian_bound (n : ℕ) (m : Fin n → ℝ)
    {u B C : ℝ} (hu : 0 ≤ u) (hB0 : 0 ≤ B)
    (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ u) (hmono : Monotone m)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f)
    (hB : ∀ z, |rootGradient n f z| ≤ B) (hC : ∀ z, |rootHessian n f z| ≤ C)
    (x : ℝ) : |rootHessian 0 (hierarchyPressure n m f) x| ≤ C+2*u*B^2 := by
  rw [hierarchyPressure_rootHessian n m u hf]
  apply hierarchyAverage_abs_le n m hf
  intro z
  have hP := rootGradient_penalty_bound_general n m hu hm hmu hmono hf hB z
  have hsq : (rootGradient n f z)^2 ≤ B^2 := by
    nlinarith [(abs_le.mp (hB z)).1,(abs_le.mp (hB z)).2,sq_nonneg (B-rootGradient n f z),
      sq_nonneg (B+rootGradient n f z)]
  calc
    |rootResponse n m u f z| ≤ |rootHessian n f z|+|u*(rootGradient n f z)^2|+
        |rootGradient n f z*rootGradient n (hierarchyPenalty n m u f) z| := by
      unfold rootResponse
      exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ C+u*B^2+B*(u*B) := by
      rw [abs_mul u _,abs_of_nonneg hu,abs_of_nonneg (sq_nonneg (rootGradient n f z)),
        abs_mul (rootGradient n f z) _]
      exact add_le_add (add_le_add (hC z) (mul_le_mul_of_nonneg_left hsq hu))
        (mul_le_mul (hB z) hP (abs_nonneg _) hB0)
    _ = C+2*u*B^2 := by ring

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarMassOne
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

theorem scalarStep_regular {f : ℝ → ℝ} (hf : BoundedDerivs f) (m v : ℝ) :
    BoundedDerivs (scalarStep m v f) := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ+v • ContinuousLinearMap.snd ℝ ℝ ℝ
  exact (hf.compCLM L).gaussianStep m

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianMassStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem gaussianMassBound_pos (B : ℝ) : 0 < gaussianMassBound B :=
  div_pos (integral_exp_pos (integrable_exp_mul_abs_gaussian (B+2)))
    (integral_exp_pos (integrable_exp_mul_abs_gaussian (-B)))

theorem gaussian_tilted_variance_bound {X : ℝ → ℝ} (hX : Continuous X)
    {v B m : ℝ} (hv : 0 ≤ v) (hvB : v ≤ B) (hm : |m| ≤ 1)
    (hb : ∀ y, |X y| ≤ v* |y|) :
    variance X ((gaussianReal 0 1).tilted (fun y => m*X y)) ≤
      gaussianMassBound B*v^2 := by
  let ν := gaussianReal 0 1
  let D := ∫ y : ℝ, Real.exp (-B* |y|) ∂ν
  let A := ∫ y : ℝ, Real.exp ((B+2)* |y|) ∂ν
  let Z := ∫ y, Real.exp (m*X y) ∂ν
  have hB : 0 ≤ B := hv.trans hvB
  have hd : 0 < D := integral_exp_pos (integrable_exp_mul_abs_gaussian (-B))
  have hA : 0 < A := integral_exp_pos (integrable_exp_mul_abs_gaussian (B+2))
  have hmb (y : ℝ) : |m*X y| ≤ B* |y| := by
    rw [abs_mul]
    calc
      |m| * |X y| ≤ |X y| := by nlinarith [abs_nonneg (X y)]
      _ ≤ v* |y| := hb y
      _ ≤ B* |y| := mul_le_mul_of_nonneg_right hvB (abs_nonneg y)
  have he (y : ℝ) : Real.exp (m*X y) ≤ Real.exp (B* |y|) :=
    Real.exp_le_exp.mpr ((le_abs_self _).trans (hmb y))
  have hi : Integrable (fun y => Real.exp (m*X y)) ν := by
    apply (integrable_exp_mul_abs_gaussian B).mono'
      (Real.continuous_exp.comp (continuous_const.mul hX)).aestronglyMeasurable
    exact ae_of_all _ (fun y => by simpa only [Function.comp_apply,Pi.mul_apply,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using he y)
  have hDZ : D ≤ Z := by
    have H := gaussian_exp_integral_bounds (fun y => m*X y) (continuous_const.mul hX) (A := 0) hB
      (fun y => by simpa using hmb y)
    simpa only [neg_zero,Real.exp_zero,one_mul] using H.1
  have hZ : 0 < Z := hd.trans_le hDZ
  let : IsProbabilityMeasure (ν.tilted (fun y => m*X y)) := isProbabilityMeasure_tilted hi
  have hb2 (y : ℝ) : (X y)^2*Real.exp (m*X y) ≤ v^2*Real.exp ((B+2)* |y|) := by
    have hs : (X y)^2 ≤ v^2* |y|^2 := by
      have H := sq_le_sq₀ (abs_nonneg (X y)) (mul_nonneg hv (abs_nonneg y)) |>.mpr (hb y)
      simpa only [sq_abs,mul_pow] using H
    have hy : |y| ≤ Real.exp |y| := (le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 1)).trans (Real.add_one_le_exp |y|)
    have hy2 : |y|^2 ≤ Real.exp (2* |y|) := by
      rw [show 2* |y| = |y|+|y| by ring,Real.exp_add]
      nlinarith [Real.exp_pos |y|,abs_nonneg y]
    calc
      _ ≤ (v^2* |y|^2)*Real.exp (B* |y|) :=
        mul_le_mul hs (he y) (Real.exp_pos _).le (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ ≤ (v^2*Real.exp (2* |y|))*Real.exp (B* |y|) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hy2 (sq_nonneg v)) (Real.exp_pos _).le
      _ = _ := by rw [mul_assoc,← Real.exp_add]; congr 2; ring
  have hn : (∫ y, (X y)^2*Real.exp (m*X y) ∂ν) ≤ v^2*A := by
    rw [← integral_const_mul]
    exact integral_mono_of_nonneg (ae_of_all _ (fun y => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le))
      ((integrable_exp_mul_abs_gaussian (B+2)).const_mul (v^2)) (ae_of_all _ hb2)
  calc
    _ ≤ ∫ y, (X y)^2 ∂ν.tilted (fun y => m*X y) :=
      variance_le_expectation_sq (hX.aestronglyMeasurable.mono_ac (tilted_absolutelyContinuous _ _))
    _ = (∫ y, (X y)^2*Real.exp (m*X y) ∂ν)/Z := by
      rw [integral_tilted_mul_eq_mgf,← integral_div]
      congr 1
      funext y
      change (Real.exp (m*X y)/Z)*(X y)^2 = _
      ring
    _ ≤ (v^2*A)/Z := div_le_div_of_nonneg_right hn hZ.le
    _ ≤ (v^2*A)/D := div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg _) hA.le) hd hDZ
    _ = _ := by dsimp [gaussianMassBound,A,D,ν]; ring

section Anchored
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem gaussianStepLaw_variance_bound {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (x : E) {v B m : ℝ} (hv : 0 ≤ v) (hvB : v ≤ B) (hm : |m| ≤ 1)
    (hb : ∀ y, |f (x,y)-f (x,0)| ≤ v* |y|) :
    variance (fun y => f (x,y)) (gaussianStepLaw m f x) ≤ gaussianMassBound B*v^2 := by
  let X := fun y => f (x,y)-f (x,0)
  have hX : Continuous X := (hf.1.continuous.comp (continuous_const.prodMk continuous_id)).sub continuous_const
  have he : gaussianStepLaw m f x = (gaussianReal 0 1).tilted (fun y => m*X y) := by
    calc
      _ = (gaussianReal 0 1).tilted (fun y => m*X y+m*f (x,0)) := by
        change (gaussianReal 0 1).tilted (fun y => m*f (x,y)) = _
        apply tilted_congr
        exact ae_of_all _ (fun y => by dsimp [X]; ring)
      _ = _ := tilted_add_constant _ _ _
  let := gaussianStepLaw_probability hf m x
  have hfm : AEStronglyMeasurable (fun y => f (x,y)) (gaussianStepLaw m f x) :=
    (hf.1.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.mono_ac
      (tilted_absolutelyContinuous _ _)
  rw [← variance_sub_const hfm (f (x,0)),he]
  exact gaussian_tilted_variance_bound hX hv hvB hm hb

end Anchored

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianMassDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

section Mass
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem gaussianStep_mass_eq_dslope {f : E × ℝ → ℝ} (hf : BoundedDerivs f) (x : E) :
    (fun m => gaussianStep m f x) = dslope (cgf (fun y => f (x,y)) (gaussianReal 0 1)) 0 := by
  funext m
  by_cases hm : m = 0
  · subst m
    rw [dslope_same,deriv_cgf_zero (hf.mem_interior_integrableExpSet_section x 0)]
    simp [gaussianStep]
  · rw [dslope_of_ne _ hm]
    simp only [gaussianStep,ite_eq_right hm,positiveGaussianLogStep,slope,cgf,mgf,sub_zero,
      smul_eq_mul,vsub_eq_sub]
    simp only [zero_mul,Real.exp_zero,integral_const,Measure.real,measure_univ,
      ENNReal.toReal_one,one_smul,Real.log_one,sub_zero]
    ring

end Mass

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarMassStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Topology NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
section Gaussian
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem gaussianStep_mass_lipschitz {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (x : E) {v B : ℝ} (hv : 0 ≤ v) (hvB : v ≤ B)
    (hfv : ∀ y, |f (x,y)-f (x,0)| ≤ v * |y|)
    {a b : ℝ} (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1) :
    |gaussianStep b f x-gaussianStep a f x| ≤ gaussianMassBound B*v^2 * |b-a| := by
  have han (m : ℝ) : AnalyticAt ℝ (cgf (fun y => f (x,y)) (gaussianReal 0 1)) m :=
    analyticAt_cgf (hf.mem_interior_integrableExpSet_section x m)
  have hvar (m : ℝ) (hm : m ∈ Icc (0:ℝ) 1) :
      |iteratedDeriv 2 (cgf (fun y => f (x,y)) (gaussianReal 0 1)) m| ≤ gaussianMassBound B*v^2 := by
    rw [← variance_tilted_mul (hf.mem_interior_integrableExpSet_section x m),abs_of_nonneg (variance_nonneg _ _)]
    exact gaussianStepLaw_variance_bound hf x hv hvB (by rw [abs_of_nonneg hm.1]; exact hm.2) hfv
  have H := dslope_mass_lipschitz han (mul_nonneg (gaussianMassBound_pos B).le (sq_nonneg v)) hvar ha hb
  rw [← gaussianStep_mass_eq_dslope hf x] at H
  exact H

theorem boundedDerivs_constant (c : ℝ) : BoundedDerivs (fun _ : E => c) := by
  refine ⟨contDiff_const,0,0,le_rfl,le_rfl,?_,?_⟩
  · intro x; simp
  · intro x
    have h : fderiv ℝ (fun _ : E => c) = fun _ => (0 : E →L[ℝ] ℝ) := by
      funext y; exact fderiv_const_apply c
    simp only [h, fderiv_const_apply, ContinuousLinearMap.opNorm_zero, le_refl]

theorem gaussianStep_mono {f g : E × ℝ → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g)
    {m : ℝ} (hm : 0 ≤ m) (hfg : ∀ z, f z ≤ g z) (x : E) :
    gaussianStep m f x ≤ gaussianStep m g x := by
  by_cases hm0 : m=0
  · simp only [gaussianStep,hm0,ite_true]
    exact integral_mono (hf.hasExpGrowth.integrable_gaussian_section hf.1.continuous x)
      (hg.hasExpGrowth.integrable_gaussian_section hg.1.continuous x) (fun y => hfg (x,y))
  · simp only [gaussianStep,ite_eq_right hm0,positiveGaussianLogStep]
    apply div_le_div_of_nonneg_right _ hm
    apply Real.log_le_log (integral_exp_pos (hf.exp_integrable m x))
    exact integral_mono (hf.exp_integrable m x) (hg.exp_integrable m x)
      (fun y => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hfg (x,y)) hm))

theorem gaussianStep_uniform_nonexpansive {f g : E × ℝ → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g)
    {m ε : ℝ} (hm : 0 ≤ m) (hfg : ∀ z, |f z-g z| ≤ ε) (x : E) :
    |gaussianStep m f x-gaussianStep m g x| ≤ ε := by
  have hg' : BoundedDerivs (fun z => g z+ε) := hg.add (boundedDerivs_constant ε)
  have hf' : BoundedDerivs (fun z => f z+ε) := hf.add (boundedDerivs_constant ε)
  have H₁ := gaussianStep_mono hf hg' hm (fun z => by linarith [(abs_le.mp (hfg z)).2]) x
  have H₂ := gaussianStep_mono hg hf' hm (fun z => by linarith [(abs_le.mp (hfg z)).1]) x
  have he₁ := congrFun (gaussianStep_add_prefix hg (fun _ => ε) m) x
  have he₂ := congrFun (gaussianStep_add_prefix hf (fun _ => ε) m) x
  rw [he₁] at H₁
  rw [he₂] at H₂
  exact abs_le.mpr ⟨by linarith,by linarith⟩
end Gaussian

theorem scalarStep_mass_lipschitz {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (hLip : LipschitzWith 1 f) {v B : ℝ} (hvB : |v| ≤ B)
    {a b : ℝ} (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1) (x : ℝ) :
    |scalarStep b v f x-scalarStep a v f x| ≤ gaussianMassBound B*v^2 * |b-a| := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ+v • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hbnd (y : ℝ) : |f (x+v*y)-f (x+v*0)| ≤ |v| * |y| := by
    have H := hLip.norm_sub_le (x+v*y) (x+v*0)
    simpa only [NNReal.coe_one,one_mul,Real.norm_eq_abs,mul_zero,add_zero,add_sub_cancel_left,abs_mul] using H
  have H := gaussianStep_mass_lipschitz (hf.compCLM L) x (abs_nonneg v) hvB hbnd ha hb
  change |scalarStep b v f x-scalarStep a v f x| ≤ gaussianMassBound B*|v|^2 * |b-a| at H
  simpa only [sq_abs] using H

theorem scalarStep_uniform_nonexpansive {f g : ℝ → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g)
    {m ε : ℝ} (hm : 0 ≤ m) (hfg : ∀ z, |f z-g z| ≤ ε) (v x : ℝ) :
    |scalarStep m v f x-scalarStep m v g x| ≤ ε := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ+v • ContinuousLinearMap.snd ℝ ℝ ℝ
  exact gaussianStep_uniform_nonexpansive (hf.compCLM L) (hg.compCLM L) hm (fun z => hfg (L z)) x

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

section Congr
variable {E : Type}
theorem gaussianStep_section_congr (m : ℝ) (f g : E × ℝ → ℝ) (x y : E)
    (hfg : ∀ z, f (x,z)=g (y,z)) : gaussianStep m f x=gaussianStep m g y := by
  unfold gaussianStep positiveGaussianLogStep
  simp_rw [hfg]
end Congr

theorem scalarStep_translate (m v c : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    scalarStep m v (fun t => f (c+t)) x=scalarStep m v f (c+x) := by
  apply gaussianStep_section_congr
  intro z
  simp only [add_assoc]

theorem scalarStep_lipschitz {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) {m : ℝ} (hm : 0 ≤ m) (v : ℝ) :
    LipschitzWith K (scalarStep m v f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hb (z : ℝ) : |f ((x-y)+z)-f z| ≤ (K:ℝ)*|x-y| := by
    simpa only [Real.norm_eq_abs,add_sub_cancel_right] using hLip.norm_sub_le ((x-y)+z) z
  have H := scalarStep_uniform_nonexpansive (hf.translate (x-y)) hf hm hb v y
  rw [scalarStep_translate,sub_add_cancel] at H
  simpa only [Real.dist_eq] using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarSemigroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal
open MeasureTheory ProbabilityTheory
namespace SK.Analytic

theorem integral_gaussian_sum {g : ℝ → ℝ} (hg : Continuous g) (hG : HasExpGrowth g)
    (v w a : ℝ) (ha : a^2=v^2+w^2) :
    (∫ y, ∫ z, g (v*y+w*z) ∂gaussianReal 0 1 ∂gaussianReal 0 1) =
      ∫ y, g (a*y) ∂gaussianReal 0 1 := by
  let V : ℝ≥0 := NNReal.mk (v^2) (sq_nonneg v)
  let W : ℝ≥0 := NNReal.mk (w^2) (sq_nonneg w)
  let A : ℝ≥0 := NNReal.mk (a^2) (sq_nonneg a)
  have he : V+W=A := NNReal.eq ha.symm
  have hint : Integrable g ((gaussianReal 0 V) ∗ (gaussianReal 0 W)) := by
    rw [gaussianReal_conv_gaussianReal,zero_add]
    exact hG.integrable_gaussianMeasure hg
  have H := integral_conv hint
  rw [gaussianReal_conv_gaussianReal,zero_add,he] at H
  have hb (y : ℝ) : (∫ z, g (v*y+w*z) ∂gaussianReal 0 1) =
      ∫ z, g (v*y+z) ∂gaussianReal 0 W :=
    integral_gaussian_mul w (hg.comp (continuous_const.add continuous_id)).stronglyMeasurable
  simp_rw [hb]
  have hsm : StronglyMeasurable (fun t => ∫ z, g (t+z) ∂gaussianReal 0 W) :=
    (hg.comp (continuous_fst.add continuous_snd)).stronglyMeasurable.integral_prod_right'
  rw [integral_gaussian_mul v hsm,← H]
  exact (integral_gaussian_mul a hg.stronglyMeasurable).symm

theorem exp_mul_scalarStep {f : ℝ → ℝ} (hf : BoundedDerivs f) {m : ℝ}
    (hm : m ≠ 0) (v x : ℝ) :
    Real.exp (m*scalarStep m v f x) =
      ∫ y, Real.exp (m*f (x+v*y)) ∂gaussianReal 0 1 := by
  have hi : Integrable (fun y => Real.exp (m*f (x+v*y))) (gaussianReal 0 1) := by
    let L : ℝ →L[ℝ] ℝ := v • ContinuousLinearMap.id ℝ ℝ
    exact (((hf.translate x).compCLM L).exp_growths m).1.integrable_gaussianMeasure
      (Real.continuous_exp.comp (continuous_const.mul (hf.1.continuous.comp
        (continuous_const.add (continuous_const.mul continuous_id)))))
  simp only [scalarStep,gaussianStep,ite_eq_right hm,positiveGaussianLogStep]
  rw [mul_div_cancel₀ _ hm,Real.exp_log (integral_exp_pos hi)]

theorem scalarStep_semigroup {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (m v w a : ℝ) (ha : a^2=v^2+w^2) :
    scalarStep m v (scalarStep m w f) = scalarStep m a f := by
  funext x
  by_cases hm : m=0
  · subst m
    simp only [scalarStep,gaussianStep,ite_true]
    have H := integral_gaussian_sum (hf.translate x).1.continuous
      (hf.translate x).hasExpGrowth v w a ha
    simpa only [add_assoc, Function.comp_apply, Pi.mul_apply] using H
  · apply (mul_left_cancel₀ hm)
    apply Real.exp_injective
    rw [exp_mul_scalarStep (scalarStep_regular hf m w) hm,exp_mul_scalarStep hf hm]
    simp_rw [exp_mul_scalarStep hf hm]
    have H := integral_gaussian_sum
      (Real.continuous_exp.comp (continuous_const.mul (hf.translate x).1.continuous))
      ((hf.translate x).exp_growths m).1 v w a ha
    simpa only [add_assoc, Function.comp_apply, Pi.mul_apply] using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarTimeChain
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

def scalarTimeStep (β m : ℝ) (t : ℝ≥0) (f : ℝ → ℝ) : ℝ → ℝ :=
  scalarStep m (β*Real.sqrt (t:ℝ)) f

theorem scalarTimeStep_regular {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (β m : ℝ) (t : ℝ≥0) : BoundedDerivs (scalarTimeStep β m t f) :=
  scalarStep_regular hf _ _

theorem scalarTimeStep_lipschitz {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) {m : ℝ} (hm : 0 ≤ m) (β : ℝ) (t : ℝ≥0) :
    LipschitzWith K (scalarTimeStep β m t f) := scalarStep_lipschitz hf hLip hm _

theorem scalarTimeStep_semigroup {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (β m : ℝ) (s t : ℝ≥0) :
    scalarTimeStep β m s (scalarTimeStep β m t f) = scalarTimeStep β m (s+t) f := by
  apply scalarStep_semigroup hf
  simp only [mul_pow, NNReal.coe_add]
  rw [Real.sq_sqrt s.coe_nonneg, Real.sq_sqrt t.coe_nonneg,
    Real.sq_sqrt (add_nonneg s.coe_nonneg t.coe_nonneg), mul_add]

@[simp] theorem scalarTimeStep_zero (β m : ℝ) (f : ℝ → ℝ) : scalarTimeStep β m 0 f=f := by
  simp only [scalarTimeStep,NNReal.coe_zero,Real.sqrt_zero,mul_zero,scalarStep_zero]

def scalarTimeChain (β : ℝ) : List (ℝ × ℝ≥0) → (ℝ → ℝ) → ℝ → ℝ
  | [],f => f
  | p::ps,f => scalarTimeStep β p.1 p.2 (scalarTimeChain β ps f)

theorem scalarTimeChain_regular {f : ℝ → ℝ} (hf : BoundedDerivs f) (β : ℝ)
    (l : List (ℝ × ℝ≥0)) : BoundedDerivs (scalarTimeChain β l f) := by
  induction l with
  | nil => exact hf
  | cons p l ih => exact scalarTimeStep_regular ih _ _ _

theorem scalarTimeChain_lipschitz {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) (β : ℝ) (l : List (ℝ × ℝ≥0))
    (hm : ∀ p ∈ l, 0 ≤ p.1) : LipschitzWith K (scalarTimeChain β l f) := by
  induction l with
  | nil => exact hLip
  | cons p l ih =>
    exact scalarTimeStep_lipschitz (scalarTimeChain_regular hf β l)
      (ih (fun q hq => hm q (List.mem_cons_of_mem p hq))) (hm p (List.mem_cons_self)) _ _

theorem scalarTimeChain_append (β : ℝ) (l₁ l₂ : List (ℝ × ℝ≥0)) (f : ℝ → ℝ) :
    scalarTimeChain β (l₁++l₂) f=scalarTimeChain β l₁ (scalarTimeChain β l₂ f) := by
  induction l₁ with
  | nil => rfl
  | cons p ps ih => simp only [List.cons_append,scalarTimeChain,ih]

theorem scalarTimeChain_ofFn (β : ℝ) (n : ℕ) (m : Fin n → ℝ) (t : Fin n → ℝ≥0)
    (f : ℝ → ℝ) :
    scalarTimeChain β (List.ofFn (fun i => (m i,t i))) f=
      scalarHierarchy n m (fun i => β*Real.sqrt (t i:ℝ)) f := by
  induction n generalizing f with
  | zero => simp [scalarTimeChain,scalarHierarchy]
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, scalarTimeChain_append]
    exact ih _ _ _

theorem scalarTimeStep_mass_lipschitz {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (hLip : LipschitzWith 1 f) (β : ℝ) {t : ℝ≥0} (ht : t ≤ 1)
    {m m' : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (hm' : m' ∈ Icc (0:ℝ) 1) (x : ℝ) :
    |scalarTimeStep β m' t f x-scalarTimeStep β m t f x| ≤
      gaussianMassBound |β| * β^2 * (t:ℝ) * |m'-m| := by
  have hst : Real.sqrt (t:ℝ) ≤ 1 := (Real.sqrt_le_one).mpr ht
  have hv : |β*Real.sqrt (t:ℝ)| ≤ |β| := by
    rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_of_le_one_right (abs_nonneg _) hst
  have H := scalarStep_mass_lipschitz hf hLip hv hm hm' x
  simpa only [scalarTimeStep,mul_pow,Real.sq_sqrt t.coe_nonneg,mul_assoc] using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_DyadicScalar
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

theorem scalarTimeChain_uniform_nonexpansive {f g : ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedDerivs g) (β : ℝ)
    (l : List (ℝ × ℝ≥0)) (hm : ∀ p ∈ l, 0 ≤ p.1) {ε : ℝ}
    (hε : ∀ x, |f x-g x| ≤ ε) (x : ℝ) :
    |scalarTimeChain β l f x-scalarTimeChain β l g x| ≤ ε := by
  induction l generalizing x with
  | nil => exact hε x
  | cons p l ih =>
    exact scalarStep_uniform_nonexpansive (scalarTimeChain_regular hf β l)
      (scalarTimeChain_regular hg β l) (hm p (List.mem_cons_self))
      (fun z => ih (fun q hq => hm q (List.mem_cons_of_mem p hq)) z) _ x

def dyadicScalar (β : ℝ) (α : ℝ → ℝ) (n : ℕ) (s : ℝ)
    (t : ℝ≥0) (f : ℝ → ℝ) : ℝ → ℝ :=
  scalarTimeChain β (dyadicIntervals α n s t) f

@[simp] theorem dyadicScalar_zero (β : ℝ) (α : ℝ → ℝ) (s : ℝ)
    (t : ℝ≥0) (f : ℝ → ℝ) :
    dyadicScalar β α 0 s t f=scalarTimeStep β (α s) t f := rfl

@[simp] theorem dyadicScalar_succ (β : ℝ) (α : ℝ → ℝ) (n : ℕ) (s : ℝ)
    (t : ℝ≥0) (f : ℝ → ℝ) :
    dyadicScalar β α (n+1) s t f=dyadicScalar β α n s (t/2)
      (dyadicScalar β α n (s+(t:ℝ)/2) (t/2) f) := by
  exact scalarTimeChain_append β _ _ f

theorem dyadicScalar_regular {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (β : ℝ) (α : ℝ → ℝ) (n : ℕ) (s : ℝ) (t : ℝ≥0) :
    BoundedDerivs (dyadicScalar β α n s t f) := scalarTimeChain_regular hf β _

theorem dyadicScalar_lipschitz {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (n : ℕ) (s : ℝ) (t : ℝ≥0) :
    LipschitzWith K (dyadicScalar β α n s t f) :=
  scalarTimeChain_lipschitz hf hLip β _ (fun _ hp => (dyadicIntervals_mass_bounds hα n s t hp).1)

theorem dyadicScalar_uniform_nonexpansive {f g : ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedDerivs g) (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (n : ℕ) (s : ℝ) (t : ℝ≥0)
    {ε : ℝ} (hε : ∀ x, |f x-g x| ≤ ε) (x : ℝ) :
    |dyadicScalar β α n s t f x-dyadicScalar β α n s t g x| ≤ ε :=
  scalarTimeChain_uniform_nonexpansive hf hg β _
    (fun _ hp => (dyadicIntervals_mass_bounds hα n s t hp).1) hε x

theorem scalarTimeMassConstant_nonneg (β : ℝ) : 0 ≤ scalarTimeMassConstant β :=
  mul_nonneg (gaussianMassBound_pos _).le (sq_nonneg _)

theorem dyadicScalar_successive_bound {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (hLip : LipschitzWith 1 f) (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (n : ℕ) (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |dyadicScalar β α (n+1) s t f x-dyadicScalar β α n s t f x| ≤
      scalarTimeMassConstant β*(t:ℝ)/(2:ℝ)^(n+1)*(α (s+t)-α s) := by
  induction n generalizing f s t x with
  | zero =>
    simp only [dyadicScalar_succ,dyadicScalar_zero]
    have hhalf : t/2 ≤ 1 := (div_le_self (show (0:ℝ≥0) ≤ t from bot_le) (by norm_num)).trans ht
    have htc : ((t/2:ℝ≥0):ℝ)=(t:ℝ)/2 := by norm_num
    have H (z) := scalarTimeStep_mass_lipschitz hf hLip β hhalf (hα s)
      (hα (s+(t:ℝ)/2)) z
    have H' := scalarStep_uniform_nonexpansive
      (scalarTimeStep_regular hf β (α (s+(t:ℝ)/2)) (t/2))
      (scalarTimeStep_regular hf β (α s) (t/2)) (hα s).1 H
      (β*Real.sqrt ((t/2:ℝ≥0):ℝ)) x
    change |scalarTimeStep β (α s) (t/2) _ x-scalarTimeStep β (α s) (t/2) _ x| ≤ _ at H'
    rw [scalarTimeStep_semigroup hf,show t/2+t/2=t by ring] at H'
    apply H'.trans
    rw [htc,abs_of_nonneg (sub_nonneg.mpr (hmono (by linarith [t.coe_nonneg])))]
    change scalarTimeMassConstant β*((t:ℝ)/2)*(α (s+(t:ℝ)/2)-α s) ≤ _
    have hM := hmono (show s+(t:ℝ)/2 ≤ s+(t:ℝ) by linarith [t.coe_nonneg])
    have hC := scalarTimeMassConstant_nonneg β
    calc
      _  ≤  scalarTimeMassConstant β*((t:ℝ)/2)*(α (s+t)-α s) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_right hM _) (by positivity)
      _ = _ := by ring
  | succ n ih =>
    rw [dyadicScalar_succ β α (n+1) s t f,dyadicScalar_succ β α n s t f]
    have hhalf : t/2 ≤ 1 := (div_le_self (show (0:ℝ≥0) ≤ t from bot_le) (by norm_num)).trans ht
    have htc : ((t/2:ℝ≥0):ℝ)=(t:ℝ)/2 := by norm_num
    let f₁ := dyadicScalar β α (n+1) (s+(t:ℝ)/2) (t/2) f
    let f₀ := dyadicScalar β α n (s+(t:ℝ)/2) (t/2) f
    have hf₁ : BoundedDerivs f₁ := dyadicScalar_regular hf β α _ _ _
    have hf₀ : BoundedDerivs f₀ := dyadicScalar_regular hf β α _ _ _
    have hl₀ : LipschitzWith 1 f₀ := dyadicScalar_lipschitz hf hLip β hα _ _ _
    have H₁ := dyadicScalar_uniform_nonexpansive hf₁ hf₀ β hα (n+1) s (t/2)
      (fun z => ih hf hLip (s+(t:ℝ)/2) (t/2) hhalf z) x
    have H₂ := ih hf₀ hl₀ s (t/2) hhalf x
    calc
      _  ≤  |dyadicScalar β α (n+1) s (t/2) f₁ x-dyadicScalar β α (n+1) s (t/2) f₀ x|+
          |dyadicScalar β α (n+1) s (t/2) f₀ x-dyadicScalar β α n s (t/2) f₀ x| := abs_sub_le _ _ _
      _  ≤  _+_ := add_le_add H₁ H₂
      _ = _ := by rw [htc,show s+(t:ℝ)/2+(t:ℝ)/2=s+t by ring,pow_succ (2:ℝ) (n+1)]; ring

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

def rootTranslate (n : ℕ) (t : ℝ) (f : ParameterSpace n → ℝ) : ParameterSpace n → ℝ :=
  fun z => f (t • parameterAxis n+z)

theorem rootGradient_translate (n : ℕ) (t : ℝ) (f : ParameterSpace n → ℝ)
    (z : ParameterSpace n) :
    rootGradient n (rootTranslate n t f) z=rootGradient n f (t • parameterAxis n+z) := by
  exact congrArg (fun L : ParameterSpace n →L[ℝ] ℝ => L (parameterAxis n))
    (fderiv_comp_add_left (t • parameterAxis n))

theorem rootHessian_translate (n : ℕ) (t : ℝ) (f : ParameterSpace n → ℝ)
    (z : ParameterSpace n) :
    rootHessian n (rootTranslate n t f) z=rootHessian n f (t • parameterAxis n+z) := by
  have he : fderiv ℝ (rootTranslate n t f)=fun z => fderiv ℝ f (t • parameterAxis n+z) := by
    funext z
    exact fderiv_comp_add_left _
  unfold rootHessian
  rw [he,fderiv_comp_add_left]

theorem RootSpinCurvature.translate {n : ℕ} {f : ParameterSpace n → ℝ}
    (h : RootSpinCurvature n f) (t : ℝ) : RootSpinCurvature n (rootTranslate n t f) := by
  intro z
  rw [rootHessian_translate,rootGradient_translate]
  exact h _

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

theorem RootSpinCurvature.hierarchyPressure {n : ℕ} {f : ParameterSpace n → ℝ}
    (h : RootSpinCurvature n f) (hf : BoundedDerivs f) (m : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) : RootSpinCurvature 0 (hierarchyPressure n m f) :=
  hierarchy_spin_curvature n m f hf hm h

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

theorem scalarTimeChain_eq_hierarchy (β : ℝ) (l : List (ℝ × ℝ≥0)) (f : ℝ → ℝ) :
    scalarTimeChain β l f=scalarHierarchy l.length (fun i => (l.get i).1)
      (fun i => β*Real.sqrt ((l.get i).2:ℝ)) f := by
  have he : List.ofFn (fun i => ((l.get i).1,(l.get i).2))=l := by
    simpa only [Prod.eta] using List.ofFn_get l
  have H := scalarTimeChain_ofFn β l.length (fun i => (l.get i).1) (fun i => (l.get i).2) f
  rw [he] at H
  exact H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarGeneralTerminal
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

theorem scalarStep_mass_lipschitz_general {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) {v B : ℝ} (hvB : |v| ≤ B)
    {a b : ℝ} (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1) (x : ℝ) :
    |scalarStep b v f x-scalarStep a v f x| ≤
      gaussianMassBound ((K:ℝ)*B)*(K:ℝ)^2*v^2*|b-a| := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ+v • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hB : (K:ℝ)*|v| ≤ (K:ℝ)*B := mul_le_mul_of_nonneg_left hvB K.coe_nonneg
  have hbnd (y : ℝ) : |f (x+v*y)-f (x+v*0)| ≤ ((K:ℝ)*|v|)*|y| := by
    have H := hLip.norm_sub_le (x+v*y) (x+v*0)
    simpa only [Real.norm_eq_abs,mul_zero,add_zero,add_sub_cancel_left,abs_mul,mul_assoc] using H
  have H := gaussianStep_mass_lipschitz (hf.compCLM L) x
    (mul_nonneg K.coe_nonneg (abs_nonneg v)) hB hbnd ha hb
  change |scalarStep b v f x-scalarStep a v f x| ≤
    gaussianMassBound ((K:ℝ)*B)*((K:ℝ)*|v|)^2*|b-a| at H
  simpa only [mul_pow,sq_abs,mul_assoc] using H

theorem scalarTimeMassConstantK_nonneg (β : ℝ) (K : ℝ≥0) :
    0 ≤ scalarTimeMassConstantK β K := by
  exact mul_nonneg (mul_nonneg (gaussianMassBound_pos _).le (sq_nonneg _)) (sq_nonneg _)

theorem scalarTimeStep_mass_lipschitz_general {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) (β : ℝ) {t : ℝ≥0} (ht : t ≤ 1)
    {m m' : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (hm' : m' ∈ Icc (0:ℝ) 1) (x : ℝ) :
    |scalarTimeStep β m' t f x-scalarTimeStep β m t f x| ≤
      scalarTimeMassConstantK β K * (t:ℝ) * |m'-m| := by
  have hst : Real.sqrt (t:ℝ) ≤ 1 := (Real.sqrt_le_one).mpr ht
  have hv : |β*Real.sqrt (t:ℝ)| ≤ |β| := by
    rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_of_le_one_right (abs_nonneg _) hst
  have H := scalarStep_mass_lipschitz_general hf hLip hv hm hm' x
  simpa only [scalarTimeStep,scalarTimeMassConstantK,mul_pow,Real.sq_sqrt t.coe_nonneg,mul_assoc] using H

theorem dyadicScalar_successive_bound_general {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (n : ℕ) (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |dyadicScalar β α (n+1) s t f x-dyadicScalar β α n s t f x| ≤
      scalarTimeMassConstantK β K*(t:ℝ)/(2:ℝ)^(n+1)*(α (s+t)-α s) := by
  induction n generalizing f s t x with
  | zero =>
    simp only [dyadicScalar_succ,dyadicScalar_zero]
    have hhalf : t/2 ≤ 1 := (div_le_self (show (0:ℝ≥0) ≤ t from bot_le) (by norm_num)).trans ht
    have htc : ((t/2:ℝ≥0):ℝ)=(t:ℝ)/2 := by norm_num
    have H (z) := scalarTimeStep_mass_lipschitz_general hf hLip β hhalf (hα s)
      (hα (s+(t:ℝ)/2)) z
    have H' := scalarStep_uniform_nonexpansive
      (scalarTimeStep_regular hf β (α (s+(t:ℝ)/2)) (t/2))
      (scalarTimeStep_regular hf β (α s) (t/2)) (hα s).1 H
      (β*Real.sqrt ((t/2:ℝ≥0):ℝ)) x
    change |scalarTimeStep β (α s) (t/2) _ x-scalarTimeStep β (α s) (t/2) _ x| ≤ _ at H'
    rw [scalarTimeStep_semigroup hf,show t/2+t/2=t by ring] at H'
    apply H'.trans
    rw [htc,abs_of_nonneg (sub_nonneg.mpr (hmono (by linarith [t.coe_nonneg])))]
    change scalarTimeMassConstantK β K*((t:ℝ)/2)*(α (s+(t:ℝ)/2)-α s) ≤ _
    have hM := hmono (show s+(t:ℝ)/2 ≤ s+(t:ℝ) by linarith [t.coe_nonneg])
    have hC := scalarTimeMassConstantK_nonneg β K
    calc
      _  ≤  scalarTimeMassConstantK β K*((t:ℝ)/2)*(α (s+t)-α s) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_right hM _) (by positivity)
      _ = _ := by ring
  | succ n ih =>
    rw [dyadicScalar_succ β α (n+1) s t f,dyadicScalar_succ β α n s t f]
    have hhalf : t/2 ≤ 1 := (div_le_self (show (0:ℝ≥0) ≤ t from bot_le) (by norm_num)).trans ht
    have htc : ((t/2:ℝ≥0):ℝ)=(t:ℝ)/2 := by norm_num
    let f₁ := dyadicScalar β α (n+1) (s+(t:ℝ)/2) (t/2) f
    let f₀ := dyadicScalar β α n (s+(t:ℝ)/2) (t/2) f
    have hf₁ : BoundedDerivs f₁ := dyadicScalar_regular hf β α _ _ _
    have hf₀ : BoundedDerivs f₀ := dyadicScalar_regular hf β α _ _ _
    have hl₀ : LipschitzWith K f₀ := dyadicScalar_lipschitz hf hLip β hα _ _ _
    have H₁ := dyadicScalar_uniform_nonexpansive hf₁ hf₀ β hα (n+1) s (t/2)
      (fun z => ih hf hLip (s+(t:ℝ)/2) (t/2) hhalf z) x
    have H₂ := ih hf₀ hl₀ s (t/2) hhalf x
    calc
      _  ≤  |dyadicScalar β α (n+1) s (t/2) f₁ x-dyadicScalar β α (n+1) s (t/2) f₀ x|+
          |dyadicScalar β α (n+1) s (t/2) f₀ x-dyadicScalar β α n s (t/2) f₀ x| := abs_sub_le _ _ _
      _  ≤  _+_ := add_le_add H₁ H₂
      _ = _ := by rw [htc,show s+(t:ℝ)/2+(t:ℝ)/2=s+t by ring,pow_succ (2:ℝ) (n+1)]; ring

theorem dyadicScalar_successive_geometric_general {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (n : ℕ) (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |dyadicScalar β α (n+1) s t f x-dyadicScalar β α n s t f x| ≤
      scalarTimeMassConstantK β K*(1/2:ℝ)^n := by
  have H := dyadicScalar_successive_bound_general hf hLip β hα hmono n s t ht x
  have hC := scalarTimeMassConstantK_nonneg β K
  have ht' : (t:ℝ) ≤ 1 := ht
  have ho : α (s+t)-α s ≤ 1 := by linarith [(hα (s+t)).2,(hα s).1]
  apply H.trans
  calc
    _ ≤ scalarTimeMassConstantK β K*(t:ℝ)/(2:ℝ)^(n+1) :=
      mul_le_of_le_one_right (by positivity) ho
    _ ≤ scalarTimeMassConstantK β K/(2:ℝ)^(n+1) :=
      div_le_div_of_nonneg_right (mul_le_of_le_one_right hC ht') (by positivity)
    _ = scalarTimeMassConstantK β K*(1/2:ℝ)^(n+1) := by rw [div_pow,one_pow]; ring
    _ ≤ scalarTimeMassConstantK β K*(1/2:ℝ)^n := by
      rw [pow_succ]
      nlinarith [mul_nonneg hC (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) n)]

def scalarCDFOperator (β : ℝ) (α : ℝ → ℝ) (s : ℝ) (t : ℝ≥0) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  limUnder atTop (fun n => dyadicScalar β α n s t f x)

theorem dyadicScalar_general_uniform {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    TendstoUniformly (fun n => dyadicScalar β α n s t f) (scalarCDFOperator β α s t f) atTop :=
  (geometric_uniform_limit (fun n => dyadicScalar β α n s t f)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)<1)
    (fun n x => dyadicScalar_successive_geometric_general hf hLip β hα hmono n s t ht x)).1

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_TerminalPerturbation
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

def scalarParameterTerminal (n : ℕ) (v : Fin n → ℝ) (F : ℝ → ℝ → ℝ)
    (x : ℝ) (z : ParameterSpace n) : ℝ := F (parameter n z) (x+coordinateLinear n v z)

theorem hierarchyPressure_scalarParameterTerminal (n : ℕ) (m v : Fin n → ℝ)
    (F : ℝ → ℝ → ℝ) (x a : ℝ) :
    hierarchyPressure n m (scalarParameterTerminal n v F x) a =
      scalarHierarchy n m v (F a) x := by
  induction n generalizing F with
  | zero => simp [hierarchyPressure,scalarParameterTerminal,scalarHierarchy,parameter,coordinateLinear]
  | succ n ih =>
    have he : gaussianStep (m (Fin.last n)) (scalarParameterTerminal (n+1) v F x) =
        scalarParameterTerminal n (fun i => v i.castSucc)
          (fun a => scalarStep (m (Fin.last n)) (v (Fin.last n)) (F a)) x := by
      funext z
      have harg (y : ℝ) : scalarParameterTerminal (n+1) v F x (z,y) =
          F (parameter n z) ((x+coordinateLinear n (fun i => v i.castSucc) z)+v (Fin.last n)*y) := by
        unfold scalarParameterTerminal
        rw [coordinateLinear_apply (n+1),coordinateLinear_apply n,Fin.sum_univ_castSucc]
        simp only [coordinateProjection,Fin.lastCases_castSucc,Fin.lastCases_last,parameter,
          ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',add_assoc]
      simp only [gaussianStep,positiveGaussianLogStep,scalarParameterTerminal,scalarStep]
      simp only [scalarParameterTerminal] at harg
      simp_rw [harg]
    change hierarchyPressure n (fun i => m i.castSucc) _ a = _
    rw [he,ih]
    rfl

theorem primitivePerturbation_regular {f G : ℝ → ℝ} (hf : BoundedDerivs f)
    (hG : BoundedDerivs G) (a : ℝ) : BoundedDerivs (primitivePerturbation f G a) := by
  change BoundedDerivs (fun y => f y+G (y+a)-G y)
  simpa only [neg_one_mul,sub_eq_add_neg,add_comm a] using
    (hf.add (hG.translate a)).add (hG.const_mul (-1))

theorem primitiveParameterTerminal_regular (n : ℕ) (v : Fin n → ℝ)
    {f G : ℝ → ℝ} (hf : BoundedDerivs f) (hG : BoundedDerivs G) (x : ℝ) :
    BoundedDerivs (scalarParameterTerminal n v (primitivePerturbation f G) x) := by
  have H := (((hf.translate x).compCLM (coordinateLinear n v)).add
    ((hG.translate x).compCLM (coordinateLinear n v+parameter n))).add
    (((hG.translate x).compCLM (coordinateLinear n v)).const_mul (-1))
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  simp only [scalarParameterTerminal,primitivePerturbation,add_apply,neg_one_mul,add_assoc]
  ring

theorem primitiveParameterTerminal_rootGradient (n : ℕ) (v : Fin n → ℝ)
    {f G g : ℝ → ℝ} (hf : BoundedDerivs f) (hG : BoundedDerivs G)
    (hg : ∀ y, HasDerivAt G (g y) y) (x : ℝ) (z : ParameterSpace n) :
    rootGradient n (scalarParameterTerminal n v (primitivePerturbation f G) x) z =
      g (x+coordinateLinear n v z+parameter n z) := by
  have hd := rootLine_hasDerivAt n (primitiveParameterTerminal_regular n v hf hG x) z 0
  have he : (fun a : ℝ => scalarParameterTerminal n v (primitivePerturbation f G) x
      (z+a • parameterAxis n)) = fun a =>
      f (x+coordinateLinear n v z)+G (x+coordinateLinear n v z+parameter n z+a)-
        G (x+coordinateLinear n v z) := by
    funext a
    simp only [scalarParameterTerminal,primitivePerturbation,map_add,map_smul,
      coordinateLinear_axis,parameter_axis,smul_eq_mul,mul_zero,add_zero,mul_one,add_assoc]
  rw [he,zero_smul,add_zero] at hd
  have hd' := (hg (x+coordinateLinear n v z+parameter n z+0)).comp 0
    ((hasDerivAt_id 0).const_add (x+coordinateLinear n v z+parameter n z))
  simp only [add_zero,mul_one] at hd'
  exact hd.unique ((hd'.const_add _).sub_const _)

theorem primitiveParameterTerminal_rootHessian (n : ℕ) (v : Fin n → ℝ)
    {f G g dg : ℝ → ℝ} (hf : BoundedDerivs f) (hG : BoundedDerivs G)
    (hg : ∀ y, HasDerivAt G (g y) y) (hdg : ∀ y, HasDerivAt g (dg y) y)
    (x : ℝ) (z : ParameterSpace n) :
    rootHessian n (scalarParameterTerminal n v (primitivePerturbation f G) x) z =
      dg (x+coordinateLinear n v z+parameter n z) := by
  have hd := rootGradientLine_hasDerivAt n (primitiveParameterTerminal_regular n v hf hG x) z 0
  have he : (fun a : ℝ => rootGradient n (scalarParameterTerminal n v
      (primitivePerturbation f G) x) (z+a • parameterAxis n)) = fun a =>
      g (x+coordinateLinear n v z+parameter n z+a) := by
    funext a
    rw [primitiveParameterTerminal_rootGradient n v hf hG hg]
    simp only [map_add,map_smul,coordinateLinear_axis,parameter_axis,
      smul_eq_mul,mul_zero,add_zero,mul_one,add_assoc]
  rw [he,zero_smul,add_zero] at hd
  have hd' := (hdg (x+coordinateLinear n v z+parameter n z+0)).comp 0
    ((hasDerivAt_id 0).const_add (x+coordinateLinear n v z+parameter n z))
  simp only [add_zero,mul_one] at hd'
  exact hd.unique hd'

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

theorem hierarchyPressure_rootGradient_lipschitz (n : ℕ) (m : Fin n → ℝ)
    {B C : ℝ≥0} (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (hmono : Monotone m)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f)
    (hB : ∀ z, |rootGradient n f z| ≤ B) (hC : ∀ z, |rootHessian n f z| ≤ C) :
    LipschitzWith (C+2*B^2) (rootGradient 0 (hierarchyPressure n m f)) := by
  have hf' := hierarchyPressure_boundedDerivs n m f hf
  have hd (x : ℝ) : HasDerivAt (rootGradient 0 (hierarchyPressure n m f))
      (rootHessian 0 (hierarchyPressure n m f) x) x := by
    simpa only [parameterAxis,smul_eq_mul,mul_one,zero_add] using
      rootGradientLine_hasDerivAt 0 hf' 0 x
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hd x).differentiableAt)
  intro x
  rw [(hd x).deriv]
  have H := hierarchyPressure_rootHessian_bound n m (u := 1) (by norm_num) B.coe_nonneg
    (fun i => (hm i).1) (fun i => (hm i).2) hmono hf hB hC x
  norm_num only [mul_one] at H
  exact_mod_cast H

theorem scalarHierarchy_primitive_regular (n : ℕ) (m v : Fin n → ℝ)
    {f G : ℝ → ℝ} (hf : BoundedDerivs f) (hG : BoundedDerivs G) (x : ℝ) :
    BoundedDerivs (fun a => scalarHierarchy n m v (primitivePerturbation f G a) x) := by
  have he := funext (hierarchyPressure_scalarParameterTerminal n m v (primitivePerturbation f G) x)
  rw [← he]
  exact hierarchyPressure_boundedDerivs n m _ (primitiveParameterTerminal_regular n v hf hG x)

theorem scalarHierarchy_primitive_derivative_lipschitz (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (hmono : Monotone m)
    {f G g dg : ℝ → ℝ} (hf : BoundedDerivs f) (hG : BoundedDerivs G)
    (hg : ∀ y, HasDerivAt G (g y) y) (hdg : ∀ y, HasDerivAt g (dg y) y)
    {B C : ℝ≥0} (hB : ∀ y, |g y| ≤ B) (hC : ∀ y, |dg y| ≤ C) (x : ℝ) :
    LipschitzWith (C+2*B^2) (deriv (fun a => scalarHierarchy n m v (primitivePerturbation f G a) x)) := by
  rw [← funext (hierarchyPressure_scalarParameterTerminal n m v (primitivePerturbation f G) x)]
  change LipschitzWith (C+2*B^2) (rootGradient 0 _)
  apply hierarchyPressure_rootGradient_lipschitz n m hm hmono
    (primitiveParameterTerminal_regular n v hf hG x)
  · intro z
    rw [primitiveParameterTerminal_rootGradient n v hf hG hg]
    exact hB _
  · intro z
    rw [primitiveParameterTerminal_rootHessian n v hf hG hg hdg]
    exact hC _

theorem dyadicScalar_primitive_regular (β : ℝ) (α : ℝ → ℝ) (n : ℕ) (s : ℝ) (t : ℝ≥0)
    {f G : ℝ → ℝ} (hf : BoundedDerivs f) (hG : BoundedDerivs G) (x : ℝ) :
    BoundedDerivs (fun a => dyadicScalar β α n s t (primitivePerturbation f G a) x) := by
  simp only [dyadicScalar,scalarTimeChain_eq_hierarchy]
  exact scalarHierarchy_primitive_regular _ _ _ hf hG x

theorem dyadicScalar_primitive_derivative_lipschitz (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hmono : Monotone α) (n : ℕ) (s : ℝ) (t : ℝ≥0)
    {f G g dg : ℝ → ℝ} (hf : BoundedDerivs f) (hG : BoundedDerivs G)
    (hg : ∀ y, HasDerivAt G (g y) y) (hdg : ∀ y, HasDerivAt g (dg y) y)
    {B C : ℝ≥0} (hB : ∀ y, |g y| ≤ B) (hC : ∀ y, |dg y| ≤ C) (x : ℝ) :
    LipschitzWith (C+2*B^2) (deriv (fun a => dyadicScalar β α n s t (primitivePerturbation f G a) x)) := by
  simp only [dyadicScalar,scalarTimeChain_eq_hierarchy]
  apply scalarHierarchy_primitive_derivative_lipschitz _ _ _ _ _ hf hG hg hdg hB hC x
  · intro i
    exact dyadicIntervals_mass_bounds hα n s t (List.get_mem _ i)
  · exact scalarTimeChain_mass_monotone _ (dyadicIntervals_pairwise hmono n s t)

def scalarCDFTerminalDerivative (β : ℝ) (α : ℝ → ℝ) (s : ℝ) (t : ℝ≥0)
    (f G : ℝ → ℝ) (x a : ℝ) : ℝ :=
  limUnder atTop (fun n => deriv (fun b => dyadicScalar β α n s t (primitivePerturbation f G b) x) a)

theorem dyadicScalar_primitive_uniform (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    {f G : ℝ → ℝ} (hf : BoundedDerivs f) (hG : BoundedDerivs G)
    {K B : ℝ≥0} (hfK : LipschitzWith K f) (hGB : LipschitzWith B G)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    TendstoUniformly (fun n a => dyadicScalar β α n s t (primitivePerturbation f G a) x)
      (fun a => scalarCDFOperator β α s t (primitivePerturbation f G a) x) atTop :=
  (geometric_uniform_limit (fun n a => dyadicScalar β α n s t (primitivePerturbation f G a) x)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)<1)
    (fun n a => dyadicScalar_successive_geometric_general (primitivePerturbation_regular hf hG a)
      (primitivePerturbation_lipschitz hfK hGB a) β hα hmono n s t ht x)).1

theorem dyadicScalar_terminal_derivative_uniform (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    {f G g dg : ℝ → ℝ} (hf : BoundedDerivs f) (hG : BoundedDerivs G)
    (hg : ∀ y, HasDerivAt G (g y) y) (hdg : ∀ y, HasDerivAt g (dg y) y)
    {K B C : ℝ≥0} (hfK : LipschitzWith K f) (hGB : LipschitzWith B G)
    (hB : ∀ y, |g y| ≤ B) (hC : ∀ y, |dg y| ≤ C)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    TendstoUniformly (fun n => deriv (fun a => dyadicScalar β α n s t (primitivePerturbation f G a) x))
      (scalarCDFTerminalDerivative β α s t f G x) atTop := by
  apply uniformCauchySeq_limUnder
  apply uniformCauchySeq_derivative (C+2*B^2)
    (fun n a => (dyadicScalar_primitive_regular β α n s t hf hG x).1.differentiable (by decide) a |>.hasDerivAt)
    (fun n => dyadicScalar_primitive_derivative_lipschitz β hα hmono n s t hf hG hg hdg hB hC x)
  exact (dyadicScalar_primitive_uniform β hα hmono hf hG hfK hGB s t ht x).tendstoUniformlyOn.uniformCauchySeqOn

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

def scalarStepAverage (m v : ℝ) (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  gaussianAverage m (fun z : ℝ × ℝ => f (z.1+v*z.2))
    (fun z => g (z.1+v*z.2)) x

def scalarHierarchyAverage : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ) →
    (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ
  | 0,_,_,_,g => g
  | n+1,m,v,f,g => scalarHierarchyAverage n (fun i => m i.castSucc) (fun i => v i.castSucc)
      (scalarStep (m (Fin.last n)) (v (Fin.last n)) f)
      (scalarStepAverage (m (Fin.last n)) (v (Fin.last n)) f g)

theorem scalarParameterTerminal_succ (n : ℕ) (v : Fin (n+1) → ℝ)
    (F : ℝ → ℝ → ℝ) (x : ℝ) (z : ParameterSpace n) (y : ℝ) :
    scalarParameterTerminal (n+1) v F x (z,y) =
      F (parameter n z) ((x+coordinateLinear n (fun i => v i.castSucc) z)+v (Fin.last n)*y) := by
  unfold scalarParameterTerminal
  rw [coordinateLinear_apply (n+1),coordinateLinear_apply n,Fin.sum_univ_castSucc]
  simp only [coordinateProjection,Fin.lastCases_castSucc,Fin.lastCases_last,parameter,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',add_assoc]

theorem gaussianStep_scalarParameterTerminal (n : ℕ) (m : ℝ) (v : Fin (n+1) → ℝ)
    (F : ℝ → ℝ → ℝ) (x : ℝ) :
    gaussianStep m (scalarParameterTerminal (n+1) v F x) =
      scalarParameterTerminal n (fun i => v i.castSucc)
        (fun a => scalarStep m (v (Fin.last n)) (F a)) x := by
  funext z
  simp only [gaussianStep,positiveGaussianLogStep,scalarParameterTerminal_succ]
  rfl

theorem gaussianAverage_scalarParameterTerminal (n : ℕ) (m : ℝ) (v : Fin (n+1) → ℝ)
    (F H : ℝ → ℝ → ℝ) (x : ℝ) :
    gaussianAverage m (scalarParameterTerminal (n+1) v F x)
      (scalarParameterTerminal (n+1) v H x) =
      scalarParameterTerminal n (fun i => v i.castSucc)
        (fun a => scalarStepAverage m (v (Fin.last n)) (F a) (H a)) x := by
  funext z
  simp only [gaussianAverage,gaussianStepLaw,scalarParameterTerminal_succ]
  rfl

theorem hierarchyAverage_scalarParameterTerminal (n : ℕ) (m v : Fin n → ℝ)
    (F H : ℝ → ℝ → ℝ) (x a : ℝ) :
    hierarchyAverage n m (scalarParameterTerminal n v F x) (scalarParameterTerminal n v H x) a =
      scalarHierarchyAverage n m v (F a) (H a) x := by
  induction n generalizing F H with
  | zero => simp [hierarchyAverage,scalarHierarchyAverage,scalarParameterTerminal,parameter,coordinateLinear]
  | succ n ih =>
    simp only [hierarchyAverage,gaussianStep_scalarParameterTerminal,
      gaussianAverage_scalarParameterTerminal,scalarHierarchyAverage,ih]

theorem scalarHierarchy_primitive_derivative (n : ℕ) (m v : Fin n → ℝ)
    {f G g : ℝ → ℝ} (hf : BoundedDerivs f) (hG : BoundedDerivs G)
    (hg : ∀ y, HasDerivAt G (g y) y) (x a : ℝ) :
    deriv (fun b => scalarHierarchy n m v (primitivePerturbation f G b) x) a =
      scalarHierarchyAverage n m v (primitivePerturbation f G a) (fun y => g (y+a)) x := by
  rw [← funext (hierarchyPressure_scalarParameterTerminal n m v (primitivePerturbation f G) x)]
  change rootGradient 0 _ a = _
  rw [hierarchyPressure_rootGradient n m (primitiveParameterTerminal_regular n v hf hG x)]
  have he : rootGradient n (scalarParameterTerminal n v (primitivePerturbation f G) x) =
      scalarParameterTerminal n v (fun a y => g (y+a)) x :=
    funext (primitiveParameterTerminal_rootGradient n v hf hG hg x)
  rw [he,hierarchyAverage_scalarParameterTerminal]

def dyadicScalarAverage (β : ℝ) (α : ℝ → ℝ) (n : ℕ) (s : ℝ) (t : ℝ≥0)
    (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  let l := dyadicIntervals α n s t
  scalarHierarchyAverage l.length (fun i => (l.get i).1)
    (fun i => β*Real.sqrt ((l.get i).2:ℝ)) f g x

theorem dyadicScalar_primitive_derivative_zero (β : ℝ) (α : ℝ → ℝ) (n : ℕ) (s : ℝ) (t : ℝ≥0)
    {f G g : ℝ → ℝ} (hf : BoundedDerivs f) (hG : BoundedDerivs G)
    (hg : ∀ y, HasDerivAt G (g y) y) (x : ℝ) :
    deriv (fun b => dyadicScalar β α n s t (primitivePerturbation f G b) x) 0 =
      dyadicScalarAverage β α n s t f g x := by
  simp only [dyadicScalar,scalarTimeChain_eq_hierarchy]
  rw [scalarHierarchy_primitive_derivative _ _ _ hf hG hg,primitivePerturbation_zero]
  simp only [add_zero,dyadicScalarAverage]

def scalarCDFAverage (β : ℝ) (α : ℝ → ℝ) (s : ℝ) (t : ℝ≥0) (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  limUnder atTop (fun n => dyadicScalarAverage β α n s t f g x)

theorem scalarCDFAverage_eq_terminalDerivative (β : ℝ) (α : ℝ → ℝ) (s : ℝ) (t : ℝ≥0)
    {f G g : ℝ → ℝ} (hf : BoundedDerivs f) (hG : BoundedDerivs G)
    (hg : ∀ y, HasDerivAt G (g y) y) (x : ℝ) :
    scalarCDFAverage β α s t f g x=scalarCDFTerminalDerivative β α s t f G x 0 := by
  simp only [scalarCDFAverage,scalarCDFTerminalDerivative,
    dyadicScalar_primitive_derivative_zero β α _ s t hf hG hg x]

theorem dyadicScalarAverage_tendsto (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    {f G g dg : ℝ → ℝ} (hf : BoundedDerivs f) (hG : BoundedDerivs G)
    (hg : ∀ y, HasDerivAt G (g y) y) (hdg : ∀ y, HasDerivAt g (dg y) y)
    {K B C : ℝ≥0} (hfK : LipschitzWith K f) (hGB : LipschitzWith B G)
    (hB : ∀ y, |g y| ≤ B) (hC : ∀ y, |dg y| ≤ C)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    Tendsto (fun n => dyadicScalarAverage β α n s t f g x) atTop
      (𝓝 (scalarCDFAverage β α s t f g x)) := by
  have H := (dyadicScalar_terminal_derivative_uniform β hα hmono hf hG hg hdg hfK hGB hB hC s t ht x).tendsto_at 0
  simpa only [dyadicScalar_primitive_derivative_zero β α _ s t hf hG hg x,
    ← scalarCDFAverage_eq_terminalDerivative β α s t hf hG hg x] using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

abbrev TripleMiddleIncrement := ProductIncrement (E:=ℝ × ℝ) (F:=ℝ)

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

def scalarCDFValue (β : ℝ) (α : ℝ → ℝ) (s : ℝ) (t : ℝ≥0) (x : ℝ) : ℝ :=
  limUnder atTop (fun n => dyadicScalar β α n s t scalarSpinTerminal x)

def scalarCDFGradient (β : ℝ) (α : ℝ → ℝ) (s : ℝ) (t : ℝ≥0) (x : ℝ) : ℝ :=
  limUnder atTop (fun n => rootGradient 0 (dyadicScalar β α n s t scalarSpinTerminal) x)

def scalarCDFHessian (β : ℝ) (α : ℝ → ℝ) (s : ℝ) (t : ℝ≥0) (x : ℝ) : ℝ :=
  limUnder atTop (fun n => rootHessian 0 (dyadicScalar β α n s t scalarSpinTerminal) x)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyIncrementCovariance
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

def affineHierarchyResponse (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ℝ) (i : Fin n) (x : ℝ) : ℝ :=
  (∫ z, affineMoment c U (fun s => (g s)^2) z ∂hierarchyPathLaw n m (affineLogPartition c U) x)-
    ∑ k : Fin (n+1), if i.val < k.val then hierarchyAtom n m 1 k*
      (∫ z, (hierarchyMomentLevel n m (affineLogPartition c U) (affineMoment c U g) k z)^2
        ∂hierarchyPathLaw n m (affineLogPartition c U) x) else 0

end

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_TimeChainSplit
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

theorem scalarTimeChain_split_at (β : ℝ) (α : ℝ → ℝ) (l : List (ℝ × ℝ≥0))
    (hm : ∀ p ∈ l, p.1 ∈ Icc (0:ℝ) 1) (s : ℝ) (hmodel : TimeChainModels α s l)
    (t₁ t₂ : ℝ≥0) (ht : chainDuration l=t₁+t₂) :
    ∃ l₁ l₂ : List (ℝ × ℝ≥0), chainDuration l₁=t₁ ∧ chainDuration l₂=t₂ ∧
      (∀ p ∈ l₁, p.1 ∈ Icc (0:ℝ) 1) ∧ (∀ p ∈ l₂, p.1 ∈ Icc (0:ℝ) 1) ∧
      TimeChainModels α s l₁ ∧ TimeChainModels α (s+t₁) l₂ ∧
      ∀ f : ℝ → ℝ, BoundedDerivs f →
        scalarTimeChain β l₁ (scalarTimeChain β l₂ f)=scalarTimeChain β l f := by
  induction l generalizing s t₁ t₂ with
  | nil =>
    have h0 : t₁=0 ∧ t₂=0 := (add_eq_zero.mp ht.symm)
    obtain ⟨rfl,rfl⟩ := h0
    exact ⟨[],[],rfl,rfl,by simp,by simp,trivial,trivial,fun _ _ => rfl⟩
  | cons p l ih =>
    rcases p with ⟨m,d⟩
    have hp := hm (m,d) (List.mem_cons_self)
    have hm' (p) (hp : p∈l) := hm p (List.mem_cons_of_mem _ hp)
    rcases hmodel with ⟨hcell,htail⟩
    dsimp only [chainDuration_cons] at ht
    by_cases hcut : t₁≤d
    · refine ⟨[(m,t₁)],(m,d-t₁)::l,by simp,?_,?_,?_,?_,?_,?_⟩
      · simp only [chainDuration_cons]
        have hsum : t₁+(d-t₁)=d := add_tsub_cancel_of_le hcut
        exact add_left_cancel (show t₁+((d-t₁)+chainDuration l)=t₁+t₂ by
          rw [← add_assoc,hsum,ht])
      · intro p hmem
        simp only [List.mem_singleton] at hmem
        subst p
        exact hp
      · intro p hmem
        rcases List.mem_cons.mp hmem with rfl|hmem
        · exact hp
        · exact hm' p hmem
      · constructor
        · intro z hz
          have hc : (t₁:ℝ)≤d := hcut
          exact hcell z ⟨hz.1,by linarith [hz.2]⟩
        · trivial
      · constructor
        · intro z hz
          apply hcell z
          constructor
          · exact (le_add_of_nonneg_right t₁.coe_nonneg).trans hz.1
          · rw [NNReal.coe_sub hcut] at hz
            linarith [hz.2]
        · have hstart : s+(t₁:ℝ)+((d-t₁:ℝ≥0):ℝ)=s+d := by
            rw [NNReal.coe_sub hcut]
            ring
          rw [hstart]
          exact htail
      · intro f hf
        simp only [scalarTimeChain]
        rw [scalarTimeStep_semigroup (scalarTimeChain_regular hf β l),add_tsub_cancel_of_le hcut]
    · have hdc : d≤t₁ := (le_of_not_ge hcut)
      have hsum : d+(t₁-d)=t₁ := add_tsub_cancel_of_le hdc
      have htaildur : chainDuration l=(t₁-d)+t₂ := by
        apply add_left_cancel (a:=d)
        rw [← add_assoc,hsum,ht]
      obtain ⟨l₁,l₂,h₁,h₂,hm₁,hm₂,ht₁,ht₂,he⟩ := ih hm' (s+d) htail (t₁-d) t₂ htaildur
      refine ⟨(m,d)::l₁,l₂,?_,h₂,?_,hm₂,?_,?_,?_⟩
      · simp only [chainDuration_cons,h₁,hsum]
      · intro p hmem
        rcases List.mem_cons.mp hmem with rfl|hmem
        · exact hp
        · exact hm₁ p hmem
      · exact ⟨hcell,ht₁⟩
      · have hstart : s+(d:ℝ)+((t₁-d:ℝ≥0):ℝ)=s+t₁ := by
          rw [NNReal.coe_sub hdc]
          ring
        rw [hstart] at ht₂
        exact ht₂
      · intro f hf
        simp only [scalarTimeChain,he f hf]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_BoundedPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Topology NNReal ContDiff
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem boundedDerivs_of_derivatives {f g dg : ℝ → ℝ}
    (hg : ∀ x, HasDerivAt f (g x) x) (hdg : ∀ x, HasDerivAt g (dg x) x)
    (hcont : Continuous dg) {B C : ℝ≥0}
    (hB : ∀ x, |g x| ≤ B) (hC : ∀ x, |dg x| ≤ C) : BoundedDerivs f := by
  have he : deriv f=g := funext (fun x => (hg x).deriv)
  have he' : deriv g=dg := funext (fun x => (hdg x).deriv)
  have hgc : ContDiff ℝ 1 g := contDiff_one_iff_deriv.mpr
    ⟨fun x => (hdg x).differentiableAt,he' ▸ hcont⟩
  have hfc : ContDiff ℝ 2 f := by
    rw [show (2:ℕ∞ω)=1+1 by norm_num,contDiff_succ_iff_deriv]
    exact ⟨fun x => (hg x).differentiableAt,by norm_num,he ▸ hgc⟩
  have hfe : fderiv ℝ f=fun x => g x • (ContinuousLinearMap.id ℝ ℝ) := by
    funext x
    apply ContinuousLinearMap.ext
    intro y
    simp only [smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul,
      fderiv_eq_deriv_mul,he]
  refine ⟨hfc,B,C,B.coe_nonneg,C.coe_nonneg,?_,?_⟩
  · intro x
    rw [← norm_deriv_eq_norm_fderiv,he,Real.norm_eq_abs]
    exact hB x
  · intro x
    rw [hfe,← norm_deriv_eq_norm_fderiv,((hdg x).smul_const (ContinuousLinearMap.id ℝ ℝ)).deriv,
      norm_smul,ContinuousLinearMap.norm_id,Real.norm_eq_abs,mul_one]
    exact hC x

theorem boundedPrimitive_regular {g dg : ℝ → ℝ}
    (hg : ∀ x, HasDerivAt g (dg x) x) (hdg : Continuous dg)
    {B C : ℝ≥0} (hB : ∀ x, |g x| ≤ B) (hC : ∀ x, |dg x| ≤ C) :
    BoundedDerivs (boundedPrimitive g) :=
  boundedDerivs_of_derivatives
    (boundedPrimitive_hasDerivAt (continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt))) hg hdg hB hC

theorem dyadicScalarAverage_tendsto_C1 (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    {f g dg : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : ∀ y, HasDerivAt g (dg y) y) (hdg : Continuous dg)
    {K B C : ℝ≥0} (hfK : LipschitzWith K f)
    (hB : ∀ y, |g y| ≤ B) (hC : ∀ y, |dg y| ≤ C)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    Tendsto (fun n => dyadicScalarAverage β α n s t f g x) atTop
      (𝓝 (scalarCDFAverage β α s t f g x)) := by
  have hc : Continuous g := continuous_iff_continuousAt.mpr (fun y => (hg y).continuousAt)
  exact dyadicScalarAverage_tendsto β hα hmono hf (boundedPrimitive_regular hg hdg hB hC)
    (boundedPrimitive_hasDerivAt hc) hg hfK (boundedPrimitive_lipschitz hc hB) hB hC s t ht x

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

theorem TimeChainModels.mass_bounds {α : ℝ → ℝ} (hα : Monotone α)
    {s : ℝ} {l : List (ℝ × ℝ≥0)} (hl : TimeChainModels α s l)
    {p : ℝ × ℝ≥0} (hp : p∈l) (ht : 0<p.2) :
    α s≤p.1 ∧ p.1≤α (s+chainDuration l) := by
  induction l generalizing s with
  | nil => simp at hp
  | cons q l ih =>
    rcases q with ⟨m,d⟩
    rcases hl with ⟨hcell,htail⟩
    rcases List.mem_cons.mp hp with rfl|hp
    · have he : α s=m := hcell s ⟨le_rfl,by exact lt_add_of_pos_right s ht⟩
      refine ⟨he.le,?_⟩
      rw [← he]
      exact hα (le_add_of_nonneg_right (chainDuration ((m,d)::l)).coe_nonneg)
    · obtain ⟨h₁,h₂⟩ := ih htail hp
      refine ⟨(hα (le_add_of_nonneg_right d.coe_nonneg)).trans h₁,?_⟩
      simpa only [chainDuration_cons,NNReal.coe_add,add_assoc] using h₂

theorem scalarTimeChain_constant_error {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) (β a : ℝ) (ha : a ∈ Icc (0:ℝ) 1)
    (l : List (ℝ × ℝ≥0)) (hm : ∀ p∈l, p.1 ∈ Icc (0:ℝ) 1)
    (ht : chainDuration l≤1) {ω : ℝ}
    (hω : ∀ p∈l, 0<p.2 → |p.1-a| ≤ ω) (x : ℝ) :
    |scalarTimeChain β l f x-scalarTimeStep β a (chainDuration l) f x| ≤
      scalarTimeMassConstantK β K*(chainDuration l:ℝ)*ω := by
  induction l generalizing x with
  | nil => simp [scalarTimeChain]
  | cons p l ih =>
    rcases p with ⟨m,d⟩
    have hd : d≤1 := (le_add_of_nonneg_right (chainDuration l).coe_nonneg).trans ht
    have hl : chainDuration l≤1 := (le_add_of_nonneg_left d.coe_nonneg).trans ht
    have hm' (p) (hp:p∈l) := hm p (List.mem_cons_of_mem _ hp)
    have hω' (p) (hp:p∈l) := hω p (List.mem_cons_of_mem _ hp)
    let g := scalarTimeStep β a (chainDuration l) f
    have hg : BoundedDerivs g := scalarTimeStep_regular hf β a _
    have hLipg : LipschitzWith K g := scalarTimeStep_lipschitz hf hLip ha.1 β _
    have H₁ := scalarStep_uniform_nonexpansive (scalarTimeChain_regular hf β l) hg
      (hm (m,d) (List.mem_cons_self)).1 (fun y => ih hm' hl hω' y) (β*Real.sqrt (d:ℝ)) x
    have H₂ := scalarTimeStep_mass_lipschitz_general hg hLipg β hd ha
      (hm (m,d) (List.mem_cons_self)) x
    have Herr : scalarTimeMassConstantK β K*(d:ℝ)*|m-a| ≤ scalarTimeMassConstantK β K*(d:ℝ)*ω := by
      by_cases hd0 : d=0
      · simp [hd0]
      · exact mul_le_mul_of_nonneg_left (hω (m,d) (List.mem_cons_self) (pos_iff_ne_zero.mpr hd0))
          (mul_nonneg (scalarTimeMassConstantK_nonneg β K) d.coe_nonneg)
    rw [chainDuration_cons,← scalarTimeStep_semigroup hf]
    calc
      _ ≤ |scalarTimeStep β m d (scalarTimeChain β l f) x-scalarTimeStep β m d g x|+
          |scalarTimeStep β m d g x-scalarTimeStep β a d g x| := abs_sub_le _ _ _
      _ ≤ _+_ := add_le_add H₁ (H₂.trans Herr)
      _ = _ := by rw [NNReal.coe_add]; ring

theorem dyadicScalar_chain_error {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α) (n : ℕ)
    (l : List (ℝ × ℝ≥0)) (hm : ∀ p∈l, p.1 ∈ Icc (0:ℝ) 1)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (hdur : chainDuration l=t)
    (hmodel : TimeChainModels α s l) (x : ℝ) :
    |dyadicScalar β α n s t f x-scalarTimeChain β l f x| ≤
      scalarTimeMassConstantK β K*(t:ℝ)/(2:ℝ)^n*(α (s+t)-α s) := by
  induction n generalizing f l s t x with
  | zero =>
    simp only [dyadicScalar_zero,pow_zero,div_one,abs_sub_comm]
    rw [← hdur]
    apply scalarTimeChain_constant_error hf hLip β (α s) (hα s) l hm (hdur ▸ ht)
    intro p hp hpos
    have H := hmodel.mass_bounds hmono hp hpos
    rw [abs_of_nonneg (sub_nonneg.mpr H.1)]
    exact sub_le_sub_right H.2 _
  | succ n ih =>
    have hhalf : t/2≤1 := (div_le_self (show (0:ℝ≥0)≤t from bot_le) (by norm_num)).trans ht
    have hc : ((t/2:ℝ≥0):ℝ)=(t:ℝ)/2 := by norm_num
    have hsplit : chainDuration l=t/2+t/2 := hdur.trans (by ring)
    obtain ⟨l₁,l₂,h₁,h₂,hm₁,hm₂,ht₁,ht₂,he⟩ := scalarTimeChain_split_at β α l hm s hmodel (t/2) (t/2) hsplit
    rw [dyadicScalar_succ,← congrFun (he f hf) x]
    let g := scalarTimeChain β l₂ f
    have hg : BoundedDerivs g := scalarTimeChain_regular hf β l₂
    have hLipg : LipschitzWith K g := scalarTimeChain_lipschitz hf hLip β l₂ (fun p hp => (hm₂ p hp).1)
    have H₂ := ih hf hLip l₂ hm₂ (s+(t:ℝ)/2) (t/2) hhalf h₂ (hc ▸ ht₂)
    have H₁ := dyadicScalar_uniform_nonexpansive (dyadicScalar_regular hf β α n _ _) hg β hα n s (t/2) H₂ x
    have H₀ := ih hg hLipg l₁ hm₁ s (t/2) hhalf h₁ ht₁ x
    calc
      _ ≤ |dyadicScalar β α n s (t/2) (dyadicScalar β α n (s+(t:ℝ)/2) (t/2) f) x-
            dyadicScalar β α n s (t/2) g x|+
          |dyadicScalar β α n s (t/2) g x-scalarTimeChain β l₁ g x| := abs_sub_le _ _ _
      _ ≤ _+_ := add_le_add H₁ H₀
      _ = _ := by rw [hc,show s+(t:ℝ)/2+(t:ℝ)/2=s+t by ring,pow_succ]; ring

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarAtomic
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

def atomicScalarValue (k : ℕ) (β : ℝ) (Q : Fin (k+1) → ℝ) : ℝ :=
  scalarHierarchy (k+1) (quantileMass k)
    (fun b => β*Real.sqrt (cumulativeGapMap k Q b))
    (scalarStep 1 (β*Real.sqrt (1-Q (Fin.last k))) scalarSpinTerminal) 0

def atomicParisi (k : ℕ) (β : ℝ) (Q : Fin (k+1) → ℝ) : ℝ :=
  atomicScalarValue k β Q-(β^2/2)*∫ s in Set.Icc (0:ℝ) 1, s*quantileCDF k Q s

end SK.Analytic

end
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

theorem dyadicScalar_cdf_mass_bound {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (hLip : LipschitzWith 1 f) (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hγ : ∀ z, γ z ∈ Icc (0:ℝ) 1)
    (n : ℕ) (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |dyadicScalar β α n s t f x-dyadicScalar β γ n s t f x| ≤
      scalarTimeMassConstant β*dyadicCDFDistance α γ n s t := by
  induction n generalizing f s t x with
  | zero =>
    simp only [dyadicScalar_zero,dyadicCDFDistance]
    have H := scalarTimeStep_mass_lipschitz hf hLip β ht (hγ s) (hα s) x
    exact H.trans_eq (by dsimp [scalarTimeMassConstant]; ring)
  | succ n ih =>
    rw [dyadicScalar_succ β α n s t f,dyadicScalar_succ β γ n s t f,dyadicCDFDistance]
    have hhalf : t/2 ≤ 1 := (div_le_self (show (0:ℝ≥0) ≤ t from bot_le) (by norm_num)).trans ht
    let fα := dyadicScalar β α n (s+(t:ℝ)/2) (t/2) f
    let fγ := dyadicScalar β γ n (s+(t:ℝ)/2) (t/2) f
    have hfα : BoundedDerivs fα := dyadicScalar_regular hf β α _ _ _
    have hfγ : BoundedDerivs fγ := dyadicScalar_regular hf β γ _ _ _
    have hlγ : LipschitzWith 1 fγ := dyadicScalar_lipschitz hf hLip β hγ _ _ _
    have H₁ := dyadicScalar_uniform_nonexpansive hfα hfγ β hα n s (t/2)
      (fun z => ih hf hLip (s+(t:ℝ)/2) (t/2) hhalf z) x
    have H₂ := ih hfγ hlγ s (t/2) hhalf x
    calc
      _ ≤ |dyadicScalar β α n s (t/2) fα x-dyadicScalar β α n s (t/2) fγ x|+
          |dyadicScalar β α n s (t/2) fγ x-dyadicScalar β γ n s (t/2) fγ x| := abs_sub_le _ _ _
      _ ≤ _+_ := add_le_add H₁ H₂
      _ = _ := by ring

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

theorem dyadicScalar_cdf_mass_bound_general {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hγ : ∀ z, γ z ∈ Icc (0:ℝ) 1)
    (n : ℕ) (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |dyadicScalar β α n s t f x-dyadicScalar β γ n s t f x| ≤
      scalarTimeMassConstantK β K*dyadicCDFDistance α γ n s t := by
  induction n generalizing f s t x with
  | zero =>
    simp only [dyadicScalar_zero,dyadicCDFDistance]
    have H := scalarTimeStep_mass_lipschitz_general hf hLip β ht (hγ s) (hα s) x
    exact H.trans_eq (by dsimp [scalarTimeMassConstantK]; ring)
  | succ n ih =>
    rw [dyadicScalar_succ β α n s t f,dyadicScalar_succ β γ n s t f,dyadicCDFDistance]
    have hhalf : t/2 ≤ 1 := (div_le_self (show (0:ℝ≥0) ≤ t from bot_le) (by norm_num)).trans ht
    let fα := dyadicScalar β α n (s+(t:ℝ)/2) (t/2) f
    let fγ := dyadicScalar β γ n (s+(t:ℝ)/2) (t/2) f
    have hfα : BoundedDerivs fα := dyadicScalar_regular hf β α _ _ _
    have hfγ : BoundedDerivs fγ := dyadicScalar_regular hf β γ _ _ _
    have hlγ : LipschitzWith K fγ := dyadicScalar_lipschitz hf hLip β hγ _ _ _
    have H₁ := dyadicScalar_uniform_nonexpansive hfα hfγ β hα n s (t/2)
      (fun z => ih hf hLip (s+(t:ℝ)/2) (t/2) hhalf z) x
    have H₂ := ih hfγ hlγ s (t/2) hhalf x
    calc
      _ ≤ |dyadicScalar β α n s (t/2) fα x-dyadicScalar β α n s (t/2) fγ x|+
          |dyadicScalar β α n s (t/2) fγ x-dyadicScalar β γ n s (t/2) fγ x| := abs_sub_le _ _ _
      _ ≤ _+_ := add_le_add H₁ H₂
      _ = _ := by ring

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

def scalarCDFOverlap (β : ℝ) (α : ℝ → ℝ) (q : ℝ) : ℝ :=
  scalarCDFAverage β α 0 (Real.toNNReal q)
    (scalarCDFValue β α q (Real.toNNReal (1-q)))
    (fun z => (scalarCDFGradient β α q (Real.toNNReal (1-q)) z)^2) 0

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

def ScalarSpinConvex (f : ℝ → ℝ) : Prop :=
  ∀ x, 0 ≤ rootHessian 0 f x ∧ rootHessian 0 f x ≤ 1-(rootGradient 0 f x)^2

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_OneSiteScalar
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

section Generic
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem affineLogPartition_oneConfig (L : E →L[ℝ] ℝ) (z : E) :
    affineLogPartition (fun _ : Config 1 => 0) (fun s => spin (s 0) • L) z =
      scalarSpinTerminal (L z) := by
  change _ = Real.log (2*Real.cosh (L z))
  rw [← affineLogPartition_bool L z]
  unfold affineLogPartition
  congr 1

theorem affineMoment_oneConfig (L : E →L[ℝ] ℝ) (z : E) :
    affineMoment (fun _ : Config 1 => 0) (fun s => spin (s 0) • L) (fun s => spin (s 0)) z =
      scalarMagnetization (L z) := by
  unfold affineMoment affineGibbs
  rw [← oneConfigEquiv.sum_comp (fun t : Config 1 => Real.exp (0+(spin (t 0) • L) z))]
  rw [← oneConfigEquiv.sum_comp (fun s : Config 1 =>
    Real.exp (0+(spin (s 0) • L) z) /
      (∑ t : Bool, Real.exp (0+(spin ((oneConfigEquiv t) 0) • L) z))*spin (s 0))]
  simp only [oneConfigEquiv_apply,Fintype.sum_bool,smul_apply,smul_eq_mul,
    spin,Bool.false_eq_true,ite_false,ite_true,zero_add,one_mul,neg_one_mul,mul_one,mul_neg_one]
  unfold scalarMagnetization
  rw [Real.sinh_eq,Real.cosh_eq]
  field_simp
  ring

end Generic

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_WeightedBlockFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SK.Analytic

def blockWeights (κ : ℝ) (c a t : List (ℝ × ℝ)) :
    Fin (zeroWeightChain c++constantWeightChain κ a++zeroWeightChain t).length → ℝ :=
  fun i => if i.val < c.length then 0 else if i.val < c.length+a.length then κ else 0

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleTimeBlocks
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

structure TripleTimeBlocks (α : ℝ → ℝ) (r s₁ s₂ q : ℝ) where
  common : TimeChainOn α 0 r
  before : TimeChainOn α r s₁
  active : TimeChainOn α s₁ s₂
  after : TimeChainOn α s₂ q
  tail : TimeChainOn α q 1

namespace TripleTimeBlocks
variable {α : ℝ → ℝ} {r s₁ s₂ q : ℝ} (B : TripleTimeBlocks α r s₁ s₂ q)

def front : TimeChainOn α 0 q := ((B.common.append B.before).append B.active).append B.after
def full : TimeChainOn α 0 1 := B.front.append B.tail
def early : TimeChainOn α 0 s₂ := (B.common.append B.before).append B.active

def c : List (ℝ × ℝ) := rawTimeChain B.common.chain
def b : List (ℝ × ℝ) := rawTimeChain B.before.chain
def a : List (ℝ × ℝ) := rawTimeChain B.active.chain
def d : List (ℝ × ℝ) := rawTimeChain B.after.chain
def t : List (ℝ × ℝ) := rawTimeChain B.tail.chain
def w (κ : ℝ) : List (ℝ × (ℝ × ℝ)) := zeroWeightChain B.b++constantWeightChain κ B.a++zeroWeightChain B.d

@[simp] theorem w_underlying (κ : ℝ) : weightedUnderlying (B.w κ)=B.b++B.a++B.d := by
  simp only [w,weightedUnderlying_append,weightedUnderlying_zeroWeight,constantWeightChain_underlying]

@[simp] theorem c_variance : rawVariance B.c=r := by rw [c,rawVariance_rawTimeChain,B.common.duration,sub_zero]
@[simp] theorem a_variance : rawVariance B.a=s₂-s₁ := by rw [a,rawVariance_rawTimeChain,B.active.duration]

@[simp] theorem w_variance (κ : ℝ) : weightedVariance (B.w κ)=κ^2*(s₂-s₁) := by simp [w]
@[simp] theorem w_cross (κ : ℝ) : weightedCross (B.w κ)=κ*(s₂-s₁) := by simp [w]
@[simp] theorem w_absCross (κ : ℝ) : weightedAbsCross (B.w κ)=|κ| *(s₂-s₁) := by simp [w]

end TripleTimeBlocks

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_OverlapModulus
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

def cdfGradientTest (β : ℝ) (α : ℝ → ℝ) (s : ℝ) : ℝ :=
  s-scalarCDFOverlap β α (projIcc 0 1 (by norm_num) s)

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

def replicaGram {n d : ℕ} (s : ReplicaConfig n d) (a b : Fin d) : ℝ := overlap (s a) (s b)

def matrixReplicaSet (n d : ℕ) (D : Fin d → Fin d → ℝ) : Finset (ReplicaConfig n d) := by
  classical
  exact Finset.univ.filter (fun s => replicaGram s=D)

@[simp] theorem mem_matrixReplicaSet {n d : ℕ} (D : Fin d → Fin d → ℝ) (s : ReplicaConfig n d) :
    s∈matrixReplicaSet n d D ↔ replicaGram s=D := by
  classical
  simp [matrixReplicaSet]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_BoundedObservableCurvature
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

def RootBoundedCurvature (n : ℕ) (f : ParameterSpace n → ℝ) : Prop :=
  ∀ z, 0 ≤ rootHessian n f z ∧ rootHessian n f z ≤ 1-(rootGradient n f z)^2

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_ReplicaFlip
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

@[simp] theorem replicaFlip_involutive {n d : ℕ} (a : Fin d) :
    Function.Involutive (@replicaFlip n d a) := by
  intro s
  funext i
  by_cases hi : i=a <;> simp [replicaFlip,hi]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_ReplicaCoordinates
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

def tripleR {n : ℕ} (s : ReplicaConfig n 3) : ℝ := (overlap (s 0) (s 1)+overlap (s 0) (s 2))/2
def tripleDelta {n : ℕ} (s : ReplicaConfig n 3) : ℝ := (overlap (s 0) (s 1)-overlap (s 0) (s 2))/2
def tripleQ {n : ℕ} (s : ReplicaConfig n 3) : ℝ := overlap (s 1) (s 2)

@[simp] theorem tripleQ_flip {n : ℕ} (s : ReplicaConfig n 3) :
    tripleQ (replicaFlip 0 s)=tripleQ s := by simp [tripleQ,replicaFlip]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowGibbsGap
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

def narrowLockingSet (n : ℕ) (μ : ProbabilityMeasure ℝ) (t₀ ρ : ℝ) : Finset (ReplicaConfig n 3) := by
  classical
  exact Finset.univ.filter (fun s => tripleR s∈Ioo (t₀/2) (3*t₀) ∧
    (μ : Measure ℝ).real (Icc (tripleR s-ρ^8) (tripleR s+ρ^8))≤ρ^4 ∧
    tripleR s+ρ≤tripleQ s ∧ ρ^20≤|tripleDelta s| ∧ |tripleDelta s|≤2*ρ^20)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_GreedyRecursion
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

def bankPick {n : ℕ} (pool : ℕ → Finset (Config n)) (fallback : ℕ → Config n)
    (B : ℕ) (x : ℕ → Config n) (t q : ℝ)
    (j : ℕ) (v : ℕ → Config n) (u : ℕ) : Config n :=
  if h : ∃ w ∈ pool j, q ≤ overlap w (x u) ∧
      ∀ i, j/B*B ≤ i → i < j → |overlap (v i) w| ≤ 3*t
  then h.choose else fallback j

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_PathEndpoint
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

def extendPath {n m : ℕ} (s : Fin (m+1) → Config n) (k : ℕ) : Config n :=
  if h : k ≤ m then s ⟨k,by omega⟩ else s 0

def initialBankReference {n : ℕ} (pool : ℕ → Finset (Config n)) (fallback : ℕ → Config n)
    (B : ℕ) (t q : ℝ) (x : Config n) : Config n :=
  bankPick pool fallback B (fun _ => x) t q 0 fallback 0

@[simp] theorem initialBankReference_path {n : ℕ} (pool : ℕ → Finset (Config n)) (fallback : ℕ → Config n)
    (B : ℕ) (t q : ℝ) (x : ℕ → Config n) :
    initialBankReference pool fallback B t q (x 0)=bankPick pool fallback B x t q 0 fallback 0 := rfl

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

def signedLockingSet (n : ℕ) (h b : ℝ) : Finset (ReplicaConfig n 3) := by
  classical
  exact Finset.univ.filter (fun s => h≤tripleQ s ∧
    |overlap (s 0) (s 1)|≤b ∧ |overlap (s 0) (s 2)|≤b ∧
    2*(n:ℝ)^(-(1:ℝ)/100)< |overlap (s 0) (s 1)-overlap (s 0) (s 2)|)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_BankDynamics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical MeasureTheory Set
namespace SK.Analytic

def lockingUnion (n : ℕ) (μ : ProbabilityMeasure ℝ) (t ρ q b b' : ℝ) : Finset (ReplicaConfig n 3) :=
  signedLockingSet n q b ∪ signedLockingSet n b b' ∪ narrowLockingSet n μ t ρ

@[simp] theorem mem_lockingUnion (n : ℕ) (μ : ProbabilityMeasure ℝ) (t ρ q b b' : ℝ) (v : ReplicaConfig n 3) :
    v ∈ lockingUnion n μ t ρ q b b' ↔ (v ∈ signedLockingSet n q b ∨ v ∈ signedLockingSet n b b') ∨ v ∈ narrowLockingSet n μ t ρ := by
  simp only [lockingUnion,Finset.mem_union]

def bankBadVertex {n p : ℕ} (K : Fin p → ℕ) (B : ℕ) (μ : ProbabilityMeasure ℝ)
    (t ρ q b b' : ℝ) (z : BankIndex K → Config n) (x : Config n) : Prop :=
  bankCoverageBad K (blockPrior p B) t q z x ∨
    bankVertexBad (fun i : BankIndex K => i.1.val) (lockingUnion n μ t ρ q b b') z x

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_ClockEndpoint
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

def discreteMixedMass {n : ℕ} (β : ℝ) (J : Disorder n) (k : ℕ) : ℝ :=
  ∑x : Config n,if discreteDistance β J x k≤(1/4:ℝ) then gibbs β J x else 0

def continuousMixedMass {n : ℕ} (β : ℝ) (J : Disorder n) (t : ℝ) : ℝ :=
  ∑x : Config n,if continuousDistance β J x t≤(1/4:ℝ) then gibbs β J x else 0

end SK.Analytic

end
end

end OAI
end



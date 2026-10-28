-- Prove2me | Definitions.Def_OAIQ036S000
-- name    : OAIQ036S000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T04:47:27.011997+00:00
-- url     : https://prove2.me/theorems/c5add189-d02e-4780-8c58-8fd088f9f90c
-- title:
--   Definitions bundle OAIQ036S000 of the split of OpenAI, Stretched-exponential barriers for typical SK initial states
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SK.main`, carved from OpenAI's openai/math development (OpenAI, *Stretched-exponential barriers for typical SK initial states*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 283 declarations of OpenAI's Lean: 89 definitions, 7 inductive types or structures, 7 instances and 180 theorems. The definitions and types are `OAI.SK.Analytic.BankIndex`, `OAI.SK.Analytic.BankPrior`, `OAI.SK.Analytic.BankTuple`, `OAI.SK.Analytic.BlockProtected`, `OAI.SK.Analytic.BoundedDerivs`, `OAI.SK.Analytic.BoundedScalar`, `OAI.SK.Analytic.BranchIncrement`, `OAI.SK.Analytic.CascadeSpace`, `OAI.SK.Analytic.FiniteLaw`, `OAI.SK.Analytic.FiniteLaw.expect`, `OAI.SK.Analytic.FiniteLaw.iid`, `OAI.SK.Analytic.FiniteLaw.pi`, `OAI.SK.Analytic.FiniteLaw.prob`, `OAI.SK.Analytic.FiniteLaw.prod`, `OAI.SK.Analytic.FiniteLaw.uniformFin`, `OAI.SK.Analytic.FiniteMarkov.pathWeight`, `OAI.SK.Analytic.FiniteMarkov.walkWeight`, `OAI.SK.Analytic.GaussianLocallyDominated`, `OAI.SK.Analytic.GreedyRecord`, `OAI.SK.Analytic.GreedyScaleBounds`, `OAI.SK.Analytic.HasExpGrowth`, `OAI.SK.Analytic.Hessian`, `OAI.SK.Analytic.IsRetainedSuffix`, `OAI.SK.Analytic.MarkedWeightedState`, `OAI.SK.Analytic.MatrixStates`, `OAI.SK.Analytic.NarrowMiddleIncrement`, `OAI.SK.Analytic.NarrowRetainedState`, `OAI.SK.Analytic.NarrowTimeBlocks`, `OAI.SK.Analytic.NarrowTimeBlocks.b`, `OAI.SK.Analytic.NarrowTimeBlocks.c`, `OAI.SK.Analytic.NarrowTimeBlocks.common`, `OAI.SK.Analytic.NarrowTimeBlocks.front`, `OAI.SK.Analytic.NarrowTimeBlocks.full`, `OAI.SK.Analytic.NarrowTimeBlocks.j`, `OAI.SK.Analytic.NarrowTimeBlocks.k`, `OAI.SK.Analytic.NarrowTimeBlocks.l`, `OAI.SK.Analytic.NarrowTimeBlocks.middle`, `OAI.SK.Analytic.NarrowTimeBlocks.t`, `OAI.SK.Analytic.NarrowTimeBlocks.v`, `OAI.SK.Analytic.NarrowTimeBlocks.w` and 56 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability/SKBarriers, in whole or in part: `SKBarriers_Calculus_BilinearSchur`, `SKBarriers_Calculus_CubeMeasures`, `SKBarriers_Calculus_MarginalDerivatives`, `SKBarriers_Calculus_MarginalSecondDerivative`, `SKBarriers_Calculus_ParameterAlgebra`, `SKBarriers_Calculus_ParameterAverage`, `SKBarriers_Calculus_ParameterBilinear`, `SKBarriers_Calculus_ParameterCalculus`, `SKBarriers_Calculus_ParameterComposition`, `SKBarriers_Calculus_ParameterDerivatives`, `SKBarriers_Calculus_ParameterFieldMap`, `SKBarriers_Calculus_ParameterGrowth`, `SKBarriers_Calculus_ParameterIntegral`, `SKBarriers_Calculus_ParameterInverse`, `SKBarriers_Calculus_ParameterLinear`, `SKBarriers_Calculus_ParameterProduct`, `SKBarriers_Calculus_ParameterSmooth`, `SKBarriers_Calculus_ParameterSpace`, `SKBarriers_Calculus_ParameterWeakGrowth`, `SKBarriers_Dynamics_BankCoverage`, `SKBarriers_Dynamics_FiniteMarkovPath`, `SKBarriers_Dynamics_GreedyRecursion`, `SKBarriers_Dynamics_GridThreshold`, `SKBarriers_Dynamics_ProtectedBlock`, `SKBarriers_Dynamics_ProtectedStep`, `SKBarriers_Dynamics_ThresholdObstruction`, `SKBarriers_Gaussian_BoundedDerivatives`, `SKBarriers_Gaussian_ExponentialAverage`, `SKBarriers_Gaussian_ExponentialDerivatives`, `SKBarriers_Gaussian_ExponentialGrowth`, `SKBarriers_Gaussian_FiberGaussian`, `SKBarriers_Gaussian_GaussianDomination`, `SKBarriers_Gaussian_GaussianGrowth`, `SKBarriers_Gaussian_GaussianLogStep`, `SKBarriers_Gaussian_GaussianMassDerivative`, `SKBarriers_Gaussian_GaussianSecondStep`, `SKBarriers_Gaussian_GaussianStepAlgebra`, `SKBarriers_Gaussian_GaussianStepCalculus`, `SKBarriers_Gaussian_GaussianZeroMass`, `SKBarriers_Gaussian_LocalGaussian`, `SKBarriers_Gaussian_LocalMarginal`, `SKBarriers_Gaussian_LogDerivatives`, `SKBarriers_Gaussian_SmoothFamily`, `SKBarriers_Hierarchy_CascadeBlockLaw`, `SKBarriers_Hierarchy_CascadeRecursion`, `SKBarriers_Hierarchy_ConstantWeightMean`, `SKBarriers_Hierarchy_ConstantWeightStats`, `SKBarriers_Hierarchy_HierarchyRegularity`, `SKBarriers_Hierarchy_TimeChainOn`, `SKBarriers_Hierarchy_TimeChainPressureAlgebra`, `SKBarriers_Hierarchy_TimeChainSplit`, `SKBarriers_Hierarchy_TimeIncrementBridge`, `SKBarriers_Hierarchy_WeightedAugment`, `SKBarriers_Hierarchy_WeightedListBridge`, `SKBarriers_Hierarchy_WeightedListMean`, `SKBarriers_Hierarchy_WeightedSplitPath`, `SKBarriers_Interpolation_RestrictedReplicas`, `SKBarriers_Locking_NarrowRetainedFactor`, `SKBarriers_Locking_NarrowSchedule`, `SKBarriers_Locking_NarrowTimeBlocks`, `SKBarriers_Replicas_MatrixChain`, `SKBarriers_Replicas_MatrixCovarianceAlgebra`, `SKBarriers_Replicas_MatrixSKGuerra`, `SKBarriers_Replicas_MergedBranch`, `SKBarriers_Replicas_PairTerminal`, `SKBarriers_Replicas_ReplicaFlip`, `SKBarriers_Replicas_TripleRetainedStats`, `SKBarriers_Replicas_TripleSchedule`, `SKBarriers_Replicas_TripleScheduleScale`, `SKBarriers_Replicas_VectorBranch`, `SKBarriers_Scalar_GrowthOperations`, `SKBarriers_Scalar_OneSiteScalar`, `SKBarriers_Scalar_PartitionChain`, `SKBarriers_Scalar_PositiveTimeChain`, `SKBarriers_Scalar_RankOneMatrix`, `SKBarriers_Scalar_RawDerivatives`, `SKBarriers_Scalar_RegularAlgebra`, `SKBarriers_Scalar_ScalarHierarchyAverageAlgebra`, `SKBarriers_SpinGlass_Basic`, `SKBarriers_SpinGlass_DisorderPairs`, `SKBarriers_SpinGlass_FiniteLaw`, `SKBarriers_SpinGlass_FiniteProduct`, `SKBarriers_SpinGlass_GaugeSymmetry`, `SKBarriers_SpinGlass_LogPartition`, `SKBarriers_SpinGlass_SpinMonomials`.
--
--   **Imports.** It imports the published bundle `Def_SKBarriers`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ036S002` and `OAIQ036S003`; the statement `OAI.SK.Analytic.stretched_uniform_coverage`.
-- source:
--   OpenAI, Stretched-exponential barriers for typical SK initial states, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Stretched-exponential-barriers-for-typical-SK-initial-states-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability/SKBarriers at commit adc7f12

import Mathlib
import Definitions.Def_SKBarriers

section
-- module Solutions.OAIQ036_SK.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_BilinearSchur
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

def Hessian {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : E → ℝ) (x u v : E) : ℝ := fderiv ℝ (fderiv ℝ V) x u v

end SK.Analytic

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_ParameterSpace
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

@[reducible] def ParameterSpace : ℕ → Type
  | 0 => ℝ
  | n+1 => ParameterSpace n × ℝ

instance parameterNormedGroup : (n : ℕ) → NormedAddCommGroup (ParameterSpace n)
  | 0 => inferInstanceAs (NormedAddCommGroup ℝ)
  | n+1 => letI := parameterNormedGroup n; inferInstanceAs (NormedAddCommGroup (ParameterSpace n × ℝ))

instance parameterNormedSpace : (n : ℕ) → NormedSpace ℝ (ParameterSpace n)
  | 0 => inferInstanceAs (NormedSpace ℝ ℝ)
  | n+1 => letI := parameterNormedSpace n; inferInstanceAs (NormedSpace ℝ (ParameterSpace n × ℝ))

instance parameterFiniteDimensional : (n : ℕ) → FiniteDimensional ℝ (ParameterSpace n)
  | 0 => inferInstanceAs (FiniteDimensional ℝ ℝ)
  | n+1 => letI := parameterFiniteDimensional n; inferInstanceAs (FiniteDimensional ℝ (ParameterSpace n × ℝ))

def coordinateSquare : (n : ℕ) → ParameterSpace n → ℝ
  | 0, _ => 0
  | n+1, z => coordinateSquare n z.1 + z.2^2

@[simp] theorem coordinateSquare_zero (n : ℕ) : coordinateSquare n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change coordinateSquare n (0 : ParameterSpace n) + (0 : ℝ)^2 = 0
    rw [ih]
    norm_num

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

def parameter : (n : ℕ) → ParameterSpace n →L[ℝ] ℝ
  | 0 => ContinuousLinearMap.id ℝ ℝ
  | n+1 => (parameter n).comp (ContinuousLinearMap.fst ℝ (ParameterSpace n) ℝ)

def parameterAxis : (n : ℕ) → ParameterSpace n
  | 0 => 1
  | n+1 => (parameterAxis n, 0)

@[simp] theorem parameter_axis (n : ℕ) : parameter n (parameterAxis n) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

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

instance parameterMeasurable : (n : ℕ) → MeasurableSpace (ParameterSpace n)
  | 0 => inferInstanceAs (MeasurableSpace ℝ)
  | n+1 => letI := parameterMeasurable n; inferInstanceAs (MeasurableSpace (ParameterSpace n × ℝ))

instance parameterBorel : (n : ℕ) → BorelSpace (ParameterSpace n)
  | 0 => inferInstanceAs (BorelSpace ℝ)
  | n+1 => letI := parameterBorel n; inferInstanceAs (BorelSpace (ParameterSpace n × ℝ))

instance parameterSecondCountable : (n : ℕ) → SecondCountableTopology (ParameterSpace n)
  | 0 => inferInstanceAs (SecondCountableTopology ℝ)
  | n+1 => letI := parameterSecondCountable n; inferInstanceAs (SecondCountableTopology (ParameterSpace n × ℝ))

end SK.Analytic

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianDomination
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

def HasExpGrowth {E F : Type} [Norm E] [Norm F] (f : E → F) : Prop :=
  ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ C*Real.exp (M*‖x‖)

theorem integrable_exp_mul_abs_gaussian (M : ℝ) :
    Integrable (fun y : ℝ => Real.exp (M*|y|)) (gaussianReal 0 1) := by
  apply ((integrable_exp_mul_gaussianReal M).add (integrable_exp_mul_gaussianReal (-M))).mono'
    (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).aestronglyMeasurable
  filter_upwards [] with y
  change ‖Real.exp (M*|y|)‖ ≤ Real.exp (M*y)+Real.exp (-M*y)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_nonpos hy]
    have he : M*(-y) = -M*y := by ring
    rw [he]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

section GaussianDomination
variable {E F : Type} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem HasExpGrowth.gaussian_section_bound {f : E × ℝ → F} (hg : HasExpGrowth f) (R : ℝ) :
    ∃ b : ℝ → ℝ, Integrable b (gaussianReal 0 1) ∧
      ∀ x y, ‖x‖ ≤ R → ‖f (x,y)‖ ≤ b y := by
  obtain ⟨C,M,hC,hM,hg⟩ := hg
  refine ⟨fun y => C*Real.exp (M*R)*Real.exp (M*|y|),
    (integrable_exp_mul_abs_gaussian M).const_mul _, ?_⟩
  intro x y hx
  apply (hg (x,y)).trans
  change C * Real.exp (M*‖(x,y)‖) ≤ C*Real.exp (M*R)*Real.exp (M*|y|)
  rw [mul_assoc, ← Real.exp_add, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ hM
  rw [Prod.norm_def, Real.norm_eq_abs]
  exact max_le (hx.trans (le_add_of_nonneg_right (abs_nonneg _)))
    (le_add_of_nonneg_left ((norm_nonneg x).trans hx))

theorem HasExpGrowth.integrable_gaussian_section {f : E × ℝ → F}
    (hg : HasExpGrowth f) (hf : Continuous f) (x : E) :
    Integrable (fun y => f (x,y)) (gaussianReal 0 1) := by
  obtain ⟨b,hb,hbound⟩ := hg.gaussian_section_bound ‖x‖
  exact hb.mono' (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (ae_of_all _ (fun y => hbound x y le_rfl))

theorem HasExpGrowth.continuous_gaussian_integral {f : E × ℝ → F}
    (hg : HasExpGrowth f) (hf : Continuous f)
    [NormedSpace ℝ F] :
    Continuous (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) := by
  apply continuous_iff_continuousAt.mpr
  intro x₀
  obtain ⟨b,hb,hbound⟩ := hg.gaussian_section_bound (‖x₀‖+1)
  apply continuousAt_of_dominated (bound := b)
  · exact Eventually.of_forall (fun x => (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · filter_upwards [Metric.ball_mem_nhds x₀ (by norm_num : (0:ℝ)<1)] with x hx
    exact ae_of_all _ (fun y => hbound x y (by
      have hnorm : ‖x‖ ≤ ‖x-x₀‖+‖x₀‖ := by
        simpa only [sub_add_cancel] using norm_add_le (x-x₀) x₀
      rw [← dist_eq_norm] at hnorm
      have hdist : dist x x₀ < 1 := hx
      linarith))
  · exact hb
  · exact ae_of_all _ (fun y => (hf.comp (continuous_id.prodMk continuous_const)).continuousAt)

end GaussianDomination

section GaussianDifferentiation
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem hasFDerivAt_gaussian_integral (f : E × ℝ → F) (f₁ : E × ℝ → E →L[ℝ] F)
    (hf : Continuous f) (hf₁ : Continuous f₁)
    (hg : HasExpGrowth f) (hg₁ : HasExpGrowth f₁)
    (hd : ∀ x y, HasFDerivAt (fun z => f (z,y)) (f₁ (x,y)) x) (x₀ : E) :
    HasFDerivAt (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1)
      (∫ y, f₁ (x₀,y) ∂gaussianReal 0 1) x₀ := by
  obtain ⟨b,hb,hbound⟩ := hg₁.gaussian_section_bound (‖x₀‖+1)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Metric.ball x₀ 1)
    (Metric.ball_mem_nhds x₀ (by norm_num))
  · exact Eventually.of_forall (fun x => (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · exact hg.integrable_gaussian_section hf x₀
  · exact (hf₁.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact ae_of_all _ (fun y x hx => hbound x y (by
      have hnorm : ‖x‖ ≤ ‖x-x₀‖+‖x₀‖ := by
        simpa only [sub_add_cancel] using norm_add_le (x-x₀) x₀
      rw [← dist_eq_norm] at hnorm
      have hdist : dist x x₀ < 1 := hx
      linarith))
  · exact hb
  · exact ae_of_all _ (fun y x _ => hd x y)

end GaussianDifferentiation
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
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_ExponentialGrowth
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
section TwiceDifferentiable
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem contDiff_two_gaussian_integral (f : E × ℝ → F)
    (f₁ : E × ℝ → E →L[ℝ] F) (f₂ : E × ℝ → E →L[ℝ] E →L[ℝ] F)
    (hf : Continuous f) (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (hg : HasExpGrowth f) (hg₁ : HasExpGrowth f₁) (hg₂ : HasExpGrowth f₂)
    (hd : ∀ x y, HasFDerivAt (fun z => f (z,y)) (f₁ (x,y)) x)
    (hd₁ : ∀ x y, HasFDerivAt (fun z => f₁ (z,y)) (f₂ (x,y)) x) :
    ContDiff ℝ 2 (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) := by
  have hc₁ : ContDiff ℝ 1 (fun x => ∫ y, f₁ (x,y) ∂gaussianReal 0 1) := by
    apply (contDiff_succ_iff_hasFDerivAt (n := 0)).mpr
    refine ⟨fun x => ∫ y, f₂ (x,y) ∂gaussianReal 0 1, ?_, ?_⟩
    · exact contDiff_zero.mpr (hg₂.continuous_gaussian_integral hf₂)
    · exact hasFDerivAt_gaussian_integral f₁ f₂ hf₁ hf₂ hg₁ hg₂ hd₁
  apply (contDiff_succ_iff_hasFDerivAt (n := 1)).mpr
  exact ⟨_, hc₁, hasFDerivAt_gaussian_integral f f₁ hf hf₁ hg hg₁ hd⟩

end TwiceDifferentiable

section GrowthAlgebra
variable {E F G : Type} [Norm E] [Norm F] [Norm G]

theorem HasExpGrowth.congr_bound {f : E → F} (hf : HasExpGrowth f)
    {g : E → G} {K : ℝ} (hK : 0 ≤ K) (hg : ∀ z, ‖g z‖ ≤ K*‖f z‖) : HasExpGrowth g := by
  obtain ⟨C,M,hC,hM,hf⟩ := hf
  refine ⟨K*C,M,mul_nonneg hK hC,hM,?_⟩
  intro z
  exact (hg z).trans ((mul_le_mul_of_nonneg_left (hf z) hK).trans_eq (mul_assoc _ _ _).symm)

theorem HasExpGrowth.of_bounded {f : E → F} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ z, ‖f z‖ ≤ C) : HasExpGrowth f := by
  refine ⟨C,0,hC,le_rfl,?_⟩
  simpa only [zero_mul, Real.exp_zero, mul_one] using hf

theorem HasExpGrowth.norm {f : E → F} (hf : HasExpGrowth f) (hn : ∀ x, 0 ≤ ‖f x‖) :
    HasExpGrowth (fun x => ‖f x‖) := by
  obtain ⟨C,M,hC,hM,hf⟩ := hf
  refine ⟨C,M,hC,hM,?_⟩
  intro x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hn x)] using hf x

end GrowthAlgebra
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
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_Basic
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
namespace SK

def overlap {n : ℕ} (x y : Config n) : ℝ :=
  (∑ i : Fin n, spin (x i) * spin (y i)) / n

def flip {n : ℕ} (x : Config n) : Config n := fun i => !(x i)

@[simp] theorem spin_not (b : Bool) : spin (!b) = -spin b := by
  cases b <;> norm_num [spin]

@[simp] theorem spin_sq (b : Bool) : spin b ^ 2 = 1 := by
  cases b <;> norm_num [spin]

@[simp] theorem flip_flip {n : ℕ} (x : Config n) : flip (flip x) = x := by
  funext i
  simp [flip]

@[simp] theorem hamiltonian_flip {n : ℕ} (J : Disorder n) (x : Config n) :
    hamiltonian J (flip x) = hamiltonian J x := by
  simp [hamiltonian, flip]

@[simp] theorem gibbs_flip {n : ℕ} (β : ℝ) (J : Disorder n) (x : Config n) :
    gibbs β J (flip x) = gibbs β J x := by
  simp [gibbs]

@[simp] theorem overlap_flip_right {n : ℕ} (x y : Config n) :
    overlap x (flip y) = -overlap x y := by
  simp [overlap, flip, Finset.sum_neg_distrib, neg_div]

end SK
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_RawDerivatives
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
section RawDerivatives
variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [NormedSpace ℝ E] in
theorem HasExpGrowth.clm {f : E → F} (hg : HasExpGrowth f) (L : F →L[ℝ] G) :
    HasExpGrowth (fun x => L (f x)) :=
  hg.congr_bound (norm_nonneg L) (fun x => L.le_opNorm (f x))

theorem contDiff_two_gaussian_integral_fderiv
    (f : E × ℝ → F) (hf : ContDiff ℝ 2 f)
    (hg : HasExpGrowth f) (hg₁ : HasExpGrowth (fderiv ℝ f))
    (hg₂ : HasExpGrowth (fderiv ℝ (fderiv ℝ f))) :
    ContDiff ℝ 2 (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) := by
  let L := ContinuousLinearMap.inl ℝ E ℝ
  let T := (ContinuousLinearMap.compL ℝ E (E × ℝ) F).flip L
  let T₁ := (ContinuousLinearMap.compL ℝ E (E × ℝ) (E →L[ℝ] F)).flip L
  let f₁ : E × ℝ → E →L[ℝ] F := fun z => T (fderiv ℝ f z)
  let S := (ContinuousLinearMap.compL ℝ (E × ℝ) ((E × ℝ) →L[ℝ] F) (E →L[ℝ] F)) T
  let f₂ : E × ℝ → E →L[ℝ] E →L[ℝ] F := fun z => T₁ (S (fderiv ℝ (fderiv ℝ f) z))
  have hf₁ : ContDiff ℝ 1 f₁ := T.contDiff.comp (hf.fderiv_right (by norm_num))
  have hf₂ : Continuous f₂ := T₁.continuous.comp (S.continuous.comp
    ((hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞)+1 ≤ 2)).fderiv_right (m := 0) (by norm_num)).continuous)
  have hg₂T : HasExpGrowth f₂ := by
    obtain ⟨C,M,hC,hM,hg₂⟩ := hg₂
    refine ⟨‖T₁‖*‖S‖*C,M,mul_nonneg (mul_nonneg (norm_nonneg T₁) (norm_nonneg S)) hC,hM,?_⟩
    intro z
    calc
      ‖f₂ z‖ ≤ ‖T₁‖ * ‖S (fderiv ℝ (fderiv ℝ f) z)‖ := T₁.le_opNorm _
      _ ≤ ‖T₁‖ * (‖S‖ * ‖fderiv ℝ (fderiv ℝ f) z‖) :=
        mul_le_mul_of_nonneg_left (S.le_opNorm _) (norm_nonneg _)
      _ ≤ ‖T₁‖ * (‖S‖ * (C * Real.exp (M * ‖z‖))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hg₂ z) (norm_nonneg S)) (norm_nonneg _)
      _ = _ := by ring
  apply contDiff_two_gaussian_integral f f₁ f₂ hf.continuous hf₁.continuous hf₂ hg
    (hg₁.clm T) hg₂T
  · intro x y
    exact (hf.differentiable (by norm_num) (x,y)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).prodMk (hasFDerivAt_const y x))
  · intro x y
    have hd := T.hasFDerivAt.comp (x,y)
      ((hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞)+1 ≤ 2)).differentiable (by norm_num) (x,y)).hasFDerivAt
    have hxy : HasFDerivAt (fun z : E => (z,y)) L x :=
      (hasFDerivAt_id x).prodMk (hasFDerivAt_const y x)
    convert! hd.comp x hxy using 1
    all_goals try with_reducible_and_instances rfl

end RawDerivatives
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
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_MarginalDerivatives
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
section MarginalDerivatives
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def leftRestrict : ((E × ℝ) →L[ℝ] F) →L[ℝ] E →L[ℝ] F :=
  (ContinuousLinearMap.compL ℝ E (E × ℝ) F).flip (ContinuousLinearMap.inl ℝ E ℝ)

theorem leftRestrict_apply_bound (A : (E × ℝ) →L[ℝ] F) : ‖leftRestrict A‖ ≤ ‖A‖ := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_inl_le_one ℝ E ℝ) (norm_nonneg A)).trans_eq (mul_one _))

theorem leftRestrict_norm : ‖leftRestrict (E := E) (F := F)‖ ≤ 1 := by
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun A => (leftRestrict_apply_bound A).trans_eq (one_mul _).symm)

theorem leftRestrict_hasFDerivAt (f : E × ℝ → F) (hd : Differentiable ℝ f) (x : E) (y : ℝ) :
    HasFDerivAt (fun z => f (z,y)) (leftRestrict (fderiv ℝ f (x,y))) x := by
  exact (hd (x,y)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).prodMk (hasFDerivAt_const y x))

theorem fderiv_gaussian_integral (f : E × ℝ → F) (hf : ContDiff ℝ 1 f)
    (hg : HasExpGrowth f) (hg₁ : HasExpGrowth (fderiv ℝ f)) (x : E) :
    fderiv ℝ (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) x =
      ∫ y, leftRestrict (fderiv ℝ f (x,y)) ∂gaussianReal 0 1 := by
  exact (hasFDerivAt_gaussian_integral f _ hf.continuous
    (leftRestrict.continuous.comp ((hf.fderiv_right (m := 0) (by norm_num)).continuous))
    hg (hg₁.clm leftRestrict)
    (leftRestrict_hasFDerivAt f (hf.differentiable (by norm_num))) x).fderiv

theorem norm_fderiv_gaussian_integral_le (f : E × ℝ → F) (hf : ContDiff ℝ 1 f)
    (hg : HasExpGrowth f) (hg₁ : HasExpGrowth (fderiv ℝ f)) (x : E) :
    ‖fderiv ℝ (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) x‖ ≤
      ∫ y, ‖fderiv ℝ f (x,y)‖ ∂gaussianReal 0 1 := by
  rw [fderiv_gaussian_integral f hf hg hg₁ x]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono
  · exact ((hg₁.clm leftRestrict).integrable_gaussian_section
      (leftRestrict.continuous.comp ((hf.fderiv_right (m := 0) (by norm_num)).continuous)) x).norm
  · exact (hg₁.integrable_gaussian_section ((hf.fderiv_right (m := 0) (by norm_num)).continuous) x).norm
  · exact fun y => leftRestrict_apply_bound _

end MarginalDerivatives
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
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_MarginalSecondDerivative
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
section SecondMarginal
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def secondLeftRestrict :
    ((E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  leftRestrict ∘L
    ((ContinuousLinearMap.compL ℝ (E × ℝ) ((E × ℝ) →L[ℝ] ℝ) (E →L[ℝ] ℝ)) leftRestrict)

theorem secondLeftRestrict_apply_bound (B : (E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ) :
    ‖secondLeftRestrict B‖ ≤ ‖B‖ := by
  apply (leftRestrict_apply_bound _).trans
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_right leftRestrict_norm (norm_nonneg B)).trans_eq (one_mul _))

theorem secondLeftRestrict_growth {f : E × ℝ → ((E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ)}
    (hg : HasExpGrowth f) : HasExpGrowth (fun x => secondLeftRestrict (f x)) := by
  exact hg.congr_bound zero_le_one (fun x =>
    (secondLeftRestrict_apply_bound _).trans_eq (one_mul _).symm)

theorem fderiv_fderiv_gaussian_integral (f : E × ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hg : HasExpGrowth f) (hg₁ : HasExpGrowth (fderiv ℝ f))
    (hg₂ : HasExpGrowth (fderiv ℝ (fderiv ℝ f))) (x : E) :
    fderiv ℝ (fderiv ℝ (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1)) x =
      ∫ y, secondLeftRestrict (fderiv ℝ (fderiv ℝ f) (x,y)) ∂gaussianReal 0 1 := by
  have he : fderiv ℝ (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) =
      fun x => ∫ y, leftRestrict (fderiv ℝ f (x,y)) ∂gaussianReal 0 1 := by
    funext x
    exact fderiv_gaussian_integral f (hf.of_le (by norm_num)) hg hg₁ x
  rw [he]
  let T : ((E × ℝ) →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ := leftRestrict
  have hd : ∀ a b, HasFDerivAt (fun z => T (fderiv ℝ f (z,b)))
      (secondLeftRestrict (fderiv ℝ (fderiv ℝ f) (a,b))) a := by
    intro a b
    have h₁ := T.hasFDerivAt.comp (a,b)
      ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) (a,b)).hasFDerivAt
    have hxy : HasFDerivAt (fun z : E => (z,b)) (ContinuousLinearMap.inl ℝ E ℝ) a :=
      (hasFDerivAt_id a).prodMk (hasFDerivAt_const b a)
    convert! h₁.comp a hxy using 1
    all_goals try with_reducible_and_instances rfl
  apply (hasFDerivAt_gaussian_integral (fun z => T (fderiv ℝ f z)) _
    (T.continuous.comp (hf.fderiv_right (m := 1) (by norm_num)).continuous)
    (secondLeftRestrict.continuous.comp (hf.fderiv_right (m := 1) (by norm_num)
      |>.fderiv_right (m := 0) (by norm_num)).continuous)
    (hg₁.clm T) (secondLeftRestrict_growth hg₂) hd x).fderiv

theorem norm_fderiv_fderiv_gaussian_integral_le (f : E × ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hg : HasExpGrowth f) (hg₁ : HasExpGrowth (fderiv ℝ f))
    (hg₂ : HasExpGrowth (fderiv ℝ (fderiv ℝ f))) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1)) x‖ ≤
      ∫ y, ‖fderiv ℝ (fderiv ℝ f) (x,y)‖ ∂gaussianReal 0 1 := by
  rw [fderiv_fderiv_gaussian_integral f hf hg hg₁ hg₂ x]
  apply (norm_integral_le_integral_norm _).trans
  have hc := (hf.fderiv_right (m := 1) (by norm_num) |>.fderiv_right (m := 0) (by norm_num)).continuous
  apply integral_mono_of_nonneg (ae_of_all _ (fun y =>
    ContinuousLinearMap.opNorm_nonneg (secondLeftRestrict (fderiv ℝ (fderiv ℝ f) (x,y)))))
  · exact (hg₂.norm (fun z => ContinuousLinearMap.opNorm_nonneg _)).integrable_gaussian_section hc.norm x
  · exact ae_of_all _ (fun y => secondLeftRestrict_apply_bound _)

end SecondMarginal
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
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_LocalGaussian
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

def GaussianLocallyDominated {E F : Type} [Norm E] [Norm F]
    (f : E × ℝ → F) : Prop :=
  ∀ R : ℝ, ∃ b : ℝ → ℝ, Integrable b (gaussianReal 0 1) ∧
    ∀ x y, ‖x‖ ≤ R → ‖f (x,y)‖ ≤ b y

theorem GaussianLocallyDominated.of_norm_le {E F G : Type} [Norm E] [Norm F] [Norm G]
    {f : E × ℝ → F}
    (hg : GaussianLocallyDominated f) {g : E × ℝ → G} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ z, ‖g z‖ ≤ K*‖f z‖) : GaussianLocallyDominated g := by
  intro R
  obtain ⟨b,hb,hh⟩ := hg R
  exact ⟨fun y => K*b y,hb.const_mul _,fun x y hx =>
    (h (x,y)).trans (mul_le_mul_of_nonneg_left (hh x y hx) hK)⟩

section LocalGaussian
variable {E F G : Type} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup G]

theorem GaussianLocallyDominated.integrable_section {f : E × ℝ → F}
    (hg : GaussianLocallyDominated f) (hf : Continuous f) (x : E) :
    Integrable (fun y => f (x,y)) (gaussianReal 0 1) := by
  obtain ⟨b,hb,hbound⟩ := hg ‖x‖
  exact hb.mono' (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (ae_of_all _ (fun y => hbound x y le_rfl))

variable [NormedSpace ℝ F] [NormedSpace ℝ G]

theorem GaussianLocallyDominated.clm {f : E × ℝ → F}
    (hg : GaussianLocallyDominated f) (L : F →L[ℝ] G) :
    GaussianLocallyDominated (fun z => L (f z)) :=
  hg.of_norm_le (norm_nonneg L) (fun z => L.le_opNorm (f z))

theorem GaussianLocallyDominated.continuous_integral {f : E × ℝ → F}
    (hg : GaussianLocallyDominated f) (hf : Continuous f) :
    Continuous (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) := by
  apply continuous_iff_continuousAt.mpr
  intro x₀
  obtain ⟨b,hb,hbound⟩ := hg (‖x₀‖+1)
  apply continuousAt_of_dominated (bound := b)
  · exact Eventually.of_forall (fun x => (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · filter_upwards [Metric.ball_mem_nhds x₀ (by norm_num : (0:ℝ)<1)] with x hx
    exact ae_of_all _ (fun y => hbound x y (by
      have hnorm : ‖x‖ ≤ ‖x-x₀‖+‖x₀‖ := by
        simpa only [sub_add_cancel] using norm_add_le (x-x₀) x₀
      rw [← dist_eq_norm] at hnorm
      have hdist : dist x x₀ < 1 := hx
      linarith))
  · exact hb
  · exact ae_of_all _ (fun y => (hf.comp (continuous_id.prodMk continuous_const)).continuousAt)

variable [NormedSpace ℝ E]

theorem hasFDerivAt_local_gaussian_integral (f : E × ℝ → F)
    (f₁ : E × ℝ → E →L[ℝ] F) (hf : Continuous f) (hf₁ : Continuous f₁)
    (hg : GaussianLocallyDominated f) (hg₁ : GaussianLocallyDominated f₁)
    (hd : ∀ x y, HasFDerivAt (fun z => f (z,y)) (f₁ (x,y)) x) (x₀ : E) :
    HasFDerivAt (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1)
      (∫ y, f₁ (x₀,y) ∂gaussianReal 0 1) x₀ := by
  obtain ⟨b,hb,hbound⟩ := hg₁ (‖x₀‖+1)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Metric.ball x₀ 1)
    (Metric.ball_mem_nhds x₀ (by norm_num))
  · exact Eventually.of_forall (fun x => (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · exact hg.integrable_section hf x₀
  · exact (hf₁.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact ae_of_all _ (fun y x hx => hbound x y (by
      have hnorm : ‖x‖ ≤ ‖x-x₀‖+‖x₀‖ := by
        simpa only [sub_add_cancel] using norm_add_le (x-x₀) x₀
      rw [← dist_eq_norm] at hnorm
      have hdist : dist x x₀ < 1 := hx
      linarith))
  · exact hb
  · exact ae_of_all _ (fun y x _ => hd x y)

theorem contDiff_two_local_gaussian_integral (f : E × ℝ → F)
    (f₁ : E × ℝ → E →L[ℝ] F) (f₂ : E × ℝ → E →L[ℝ] E →L[ℝ] F)
    (hf : Continuous f) (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (hg : GaussianLocallyDominated f) (hg₁ : GaussianLocallyDominated f₁)
    (hg₂ : GaussianLocallyDominated f₂)
    (hd : ∀ x y, HasFDerivAt (fun z => f (z,y)) (f₁ (x,y)) x)
    (hd₁ : ∀ x y, HasFDerivAt (fun z => f₁ (z,y)) (f₂ (x,y)) x) :
    ContDiff ℝ 2 (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) := by
  have hc₁ : ContDiff ℝ 1 (fun x => ∫ y, f₁ (x,y) ∂gaussianReal 0 1) := by
    apply (contDiff_succ_iff_hasFDerivAt (n := 0)).mpr
    refine ⟨fun x => ∫ y, f₂ (x,y) ∂gaussianReal 0 1, ?_, ?_⟩
    · exact contDiff_zero.mpr (hg₂.continuous_integral hf₂)
    · exact hasFDerivAt_local_gaussian_integral f₁ f₂ hf₁ hf₂ hg₁ hg₂ hd₁
  apply (contDiff_succ_iff_hasFDerivAt (n := 1)).mpr
  exact ⟨_,hc₁,hasFDerivAt_local_gaussian_integral f f₁ hf hf₁ hg hg₁ hd⟩

theorem contDiff_two_local_gaussian_integral_fderiv (f : E × ℝ → F)
    (hf : ContDiff ℝ 2 f) (hg : GaussianLocallyDominated f)
    (hg₁ : GaussianLocallyDominated (fderiv ℝ f))
    (hg₂ : GaussianLocallyDominated (fderiv ℝ (fderiv ℝ f))) :
    ContDiff ℝ 2 (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) := by
  let L := ContinuousLinearMap.inl ℝ E ℝ
  let T := (ContinuousLinearMap.compL ℝ E (E × ℝ) F).flip L
  let T₁ := (ContinuousLinearMap.compL ℝ E (E × ℝ) (E →L[ℝ] F)).flip L
  let S := (ContinuousLinearMap.compL ℝ (E × ℝ) ((E × ℝ) →L[ℝ] F) (E →L[ℝ] F)) T
  let f₁ : E × ℝ → E →L[ℝ] F := fun z => T (fderiv ℝ f z)
  let f₂ : E × ℝ → E →L[ℝ] E →L[ℝ] F := fun z => T₁ (S (fderiv ℝ (fderiv ℝ f) z))
  have hf₁ : ContDiff ℝ 1 f₁ := T.contDiff.comp (hf.fderiv_right (by norm_num))
  have hf₂ : Continuous f₂ := T₁.continuous.comp (S.continuous.comp
    ((hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞)+1 ≤ 2)).fderiv_right (m := 0) (by norm_num)).continuous)
  have hg₂T : GaussianLocallyDominated f₂ := by
    apply hg₂.of_norm_le (K := ‖T₁‖*‖S‖) (mul_nonneg (norm_nonneg T₁) (norm_nonneg S))
    intro z
    calc
      ‖f₂ z‖ ≤ ‖T₁‖*‖S (fderiv ℝ (fderiv ℝ f) z)‖ := T₁.le_opNorm _
      _ ≤ ‖T₁‖*(‖S‖*‖fderiv ℝ (fderiv ℝ f) z‖) :=
        mul_le_mul_of_nonneg_left (S.le_opNorm _) (norm_nonneg _)
      _ = _ := by ring
  apply contDiff_two_local_gaussian_integral f f₁ f₂ hf.continuous hf₁.continuous hf₂ hg
    (hg₁.clm T) hg₂T
  · intro x y
    exact (hf.differentiable (by norm_num) (x,y)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).prodMk (hasFDerivAt_const y x))
  · intro x y
    have hd := T.hasFDerivAt.comp (x,y)
      ((hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞)+1 ≤ 2)).differentiable (by norm_num) (x,y)).hasFDerivAt
    have hxy : HasFDerivAt (fun z : E => (z,y)) L x :=
      (hasFDerivAt_id x).prodMk (hasFDerivAt_const y x)
    convert! hd.comp x hxy using 1
    all_goals try with_reducible_and_instances rfl
end LocalGaussian
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_ParameterGrowth
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

def ParamExpGrowth {P E F : Type} [Norm P] [Norm E] [Norm F]
    (f : P × E → F) : Prop :=
  ∀ R : ℝ, ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧
    ∀ p e, ‖p‖ ≤ R → ‖f (p,e)‖ ≤ C*Real.exp (M*‖e‖)

def ParamLinearGrowth {P E : Type} [Norm P] [Norm E]
    (f : P × E → ℝ) : Prop :=
  ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ p e, ‖p‖ ≤ R → |f (p,e)| ≤ C*(1+‖e‖)

theorem ParamExpGrowth.of_norm_le {P E F G : Type} [Norm P] [Norm E] [Norm F] [Norm G]
    {f : P × E → F} (hf : ParamExpGrowth f)
    {g : P × E → G} {K : ℝ} (hK : 0 ≤ K) (hg : ∀ z, ‖g z‖ ≤ K*‖f z‖) :
    ParamExpGrowth g := by
  intro R
  obtain ⟨C,M,hC,hM,hf⟩ := hf R
  refine ⟨K*C,M,mul_nonneg hK hC,hM,?_⟩
  intro p e hp
  exact (hg (p,e)).trans ((mul_le_mul_of_nonneg_left (hf p e hp) hK).trans_eq (mul_assoc _ _ _).symm)

section ParameterGrowth
variable {P E F G : Type} [NormedAddCommGroup P] [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedAddCommGroup G]

theorem ParamExpGrowth.of_bounded {f : P × E → F} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ z, ‖f z‖ ≤ C) : ParamExpGrowth f := by
  intro R
  refine ⟨C,0,hC,le_rfl,?_⟩
  intro p e _
  simpa only [zero_mul,Real.exp_zero,mul_one] using hf (p,e)

theorem ParamExpGrowth.add {f g : P × E → F} (hf : ParamExpGrowth f)
    (hg : ParamExpGrowth g) : ParamExpGrowth (fun z => f z+g z) := by
  intro R
  obtain ⟨C,M,hC,hM,hf⟩ := hf R
  obtain ⟨D,L,hD,hL,hg⟩ := hg R
  refine ⟨C+D,max M L,add_nonneg hC hD,(le_max_left M L).trans' hM,?_⟩
  intro p e hp
  calc
    _ ≤ ‖f (p,e)‖+‖g (p,e)‖ := norm_add_le _ _
    _ ≤ C*Real.exp (M*‖e‖)+D*Real.exp (L*‖e‖) := add_le_add (hf p e hp) (hg p e hp)
    _ ≤ C*Real.exp (max M L*‖e‖)+D*Real.exp (max M L*‖e‖) := by
      gcongr <;> first | exact le_max_left _ _ | exact le_max_right _ _
    _ = _ := by ring

theorem ParamExpGrowth.mul {f g : P × E → ℝ} (hf : ParamExpGrowth f)
    (hg : ParamExpGrowth g) : ParamExpGrowth (fun z => f z*g z) := by
  intro R
  obtain ⟨C,M,hC,hM,hf⟩ := hf R
  obtain ⟨D,L,hD,hL,hg⟩ := hg R
  refine ⟨C*D,M+L,mul_nonneg hC hD,add_nonneg hM hL,?_⟩
  intro p e hp
  calc
    ‖f (p,e)*g (p,e)‖ = ‖f (p,e)‖*‖g (p,e)‖ := norm_mul _ _
    _ ≤ (C*Real.exp (M*‖e‖))*(D*Real.exp (L*‖e‖)) :=
      mul_le_mul (hf p e hp) (hg p e hp) (norm_nonneg _) (by positivity)
    _ = _ := by rw [add_mul,Real.exp_add]; ring

theorem ParamExpGrowth.norm {f : P × E → F} (hf : ParamExpGrowth f) :
    ParamExpGrowth (fun z => ‖f z‖) := by
  apply hf.of_norm_le (K := 1) (by norm_num)
  intro z
  simp

theorem ParamLinearGrowth.exp_mul {f : P × E → ℝ} (hf : ParamLinearGrowth f) (m : ℝ) :
    ParamExpGrowth (fun z => Real.exp (m*f z)) := by
  intro R
  obtain ⟨C,hC,hf⟩ := hf R
  refine ⟨Real.exp (|m| *C),|m| *C,(Real.exp_pos _).le,mul_nonneg (abs_nonneg _) hC,?_⟩
  intro p e hp
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_add]
  apply Real.exp_le_exp.2
  calc
    m*f (p,e) ≤ |m*f (p,e)| := le_abs_self _
    _ = |m| *|f (p,e)| := abs_mul _ _
    _ ≤ |m| *(C*(1+‖e‖)) := mul_le_mul_of_nonneg_left (hf p e hp) (abs_nonneg m)
    _ = _ := by ring

theorem ParamLinearGrowth.expGrowth {f : P × E → ℝ} (hf : ParamLinearGrowth f) :
    ParamExpGrowth f := by
  intro R
  obtain ⟨C,hC,hf⟩ := hf R
  refine ⟨C,1,hC,by norm_num,?_⟩
  intro p e hp
  rw [one_mul,Real.norm_eq_abs]
  exact (hf p e hp).trans (mul_le_mul_of_nonneg_left (by have h := Real.add_one_le_exp ‖e‖; linarith) hC)

variable [NormedSpace ℝ F] [NormedSpace ℝ G]

theorem ParamExpGrowth.smul {f : P × E → ℝ} {g : P × E → F}
    (hf : ParamExpGrowth f) (hg : ParamExpGrowth g) : ParamExpGrowth (fun z => f z • g z) := by
  apply (hf.norm.mul hg.norm).of_norm_le (K := 1) (by norm_num)
  intro z
  simp only [norm_smul,Real.norm_eq_abs,abs_mul,abs_abs,abs_of_nonneg (norm_nonneg _),one_mul]
  exact le_rfl

theorem ParamExpGrowth.gaussian_integral {f : P × (E × ℝ) → F}
    (hf : ParamExpGrowth f) :
    ParamExpGrowth (fun z : P × E => ∫ y, f (z.1,(z.2,y)) ∂gaussianReal 0 1) := by
  intro R
  obtain ⟨C,M,hC,hM,hf⟩ := hf R
  let B := ∫ y : ℝ, Real.exp (M*|y|) ∂gaussianReal 0 1
  have hB : 0 ≤ B := integral_nonneg (fun y => (Real.exp_pos _).le)
  refine ⟨C*B,M,mul_nonneg hC hB,hM,?_⟩
  intro p e hp
  have hb : ∀ y, ‖f (p,(e,y))‖ ≤ C*Real.exp (M*‖e‖)*Real.exp (M*|y|) := by
    intro y
    apply (hf p (e,y) hp).trans
    rw [mul_assoc,← Real.exp_add,← mul_add]
    apply mul_le_mul_of_nonneg_left _ hC
    apply Real.exp_le_exp.2
    apply mul_le_mul_of_nonneg_left _ hM
    rw [Prod.norm_def,Real.norm_eq_abs]
    exact max_le_add_of_nonneg (norm_nonneg e) (abs_nonneg y)
  calc
    _ ≤ ∫ y, ‖f (p,(e,y))‖ ∂gaussianReal 0 1 := norm_integral_le_integral_norm _
    _ ≤ ∫ y, C*Real.exp (M*‖e‖)*Real.exp (M*|y|) ∂gaussianReal 0 1 :=
      integral_mono_of_nonneg (ae_of_all _ (fun _ => norm_nonneg _))
        ((integrable_exp_mul_abs_gaussian M).const_mul _) (ae_of_all _ hb)
    _ = _ := by rw [integral_const_mul]; dsimp [B]; ring
end ParameterGrowth
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_ExponentialDerivatives
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
section ExponentialDerivatives
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_exp_growth (f : E → ℝ) (hf : Differentiable ℝ f)
    (hg : HasExpGrowth (fun x => Real.exp (f x)))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ C) :
    HasExpGrowth (fderiv ℝ (fun x => Real.exp (f x))) := by
  apply hg.congr_bound hC
  intro x
  rw [fderiv_exp (hf x), norm_smul]
  exact (mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)).trans_eq (mul_comm _ _)

theorem fderiv_fderiv_exp (f : E → ℝ) (hf : ContDiff ℝ 2 f) (x : E) :
    fderiv ℝ (fderiv ℝ (fun z => Real.exp (f z))) x =
      Real.exp (f x) • fderiv ℝ (fderiv ℝ f) x +
      (Real.exp (f x) • fderiv ℝ f x).smulRight (fderiv ℝ f x) := by
  have hd := hf.differentiable (by norm_num)
  have hh : fderiv ℝ (fun z => Real.exp (f z)) = fun z => Real.exp (f z) • fderiv ℝ f z := by
    funext z
    exact fderiv_exp (hd z)
  rw [hh]
  exact ((hd x).hasFDerivAt.exp.smul
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x).hasFDerivAt).fderiv

theorem fderiv_fderiv_exp_growth (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    (hg : HasExpGrowth (fun x => Real.exp (f x)))
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    (hbb : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ D) :
    HasExpGrowth (fderiv ℝ (fderiv ℝ (fun x => Real.exp (f x)))) := by
  apply hg.congr_bound (show 0 ≤ D+C*C by positivity)
  intro x
  rw [fderiv_fderiv_exp f hf x]
  calc
    _ ≤ ‖Real.exp (f x) • fderiv ℝ (fderiv ℝ f) x‖+
        ‖(Real.exp (f x) • fderiv ℝ f x).smulRight (fderiv ℝ f x)‖ := ContinuousLinearMap.opNorm_add_le _ _
    _ ≤ ‖Real.exp (f x)‖*‖fderiv ℝ (fderiv ℝ f) x‖+
        (‖Real.exp (f x)‖*‖fderiv ℝ f x‖)*‖fderiv ℝ f x‖ := by
      rw [ContinuousLinearMap.norm_smulRight_apply]
      gcongr <;> exact ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ ‖Real.exp (f x)‖*D+(‖Real.exp (f x)‖*C)*C := by gcongr <;> first | exact hb _ | exact hbb _
    _ = _ := by ring

end ExponentialDerivatives
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
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianLogStep
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
section UniformBounds
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_le_of_fderiv_bound (f : E → ℝ) (hd : Differentiable ℝ f)
    (C : ℝ) (hC : ∀ x, ‖fderiv ℝ f x‖ ≤ C) (x : E) :
    ‖f x‖ ≤ ‖f 0‖ + C*‖x‖ := by
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun x (_ : x ∈ (Set.univ : Set E)) => hd x)
    (fun x (_ : x ∈ (Set.univ : Set E)) => hC x) convex_univ
    (mem_univ (0:E)) (mem_univ x)
  simp only [sub_zero] at h
  calc
    ‖f x‖ = ‖(f x-f 0)+f 0‖ := by rw [sub_add_cancel]
    _ ≤ ‖f x-f 0‖+‖f 0‖ := norm_add_le _ _
    _ ≤ ‖f 0‖+C*‖x‖ := by linarith

theorem exp_mul_growth_of_fderiv_bound (f : E → ℝ) (hd : Differentiable ℝ f)
    (C : ℝ) (hC₀ : 0 ≤ C) (hC : ∀ x, ‖fderiv ℝ f x‖ ≤ C) (m : ℝ) :
    HasExpGrowth (fun x => Real.exp (m*f x)) := by
  refine ⟨Real.exp (|m| *‖f 0‖), |m| *C, (Real.exp_pos _).le,
    mul_nonneg (abs_nonneg _) hC₀, ?_⟩
  intro x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hf := norm_le_of_fderiv_bound f hd C hC x
  have hb : m*f x ≤ |m| *‖f x‖ := by
    simpa only [Real.norm_eq_abs, abs_mul] using le_abs_self (m*f x)
  nlinarith [mul_le_mul_of_nonneg_left hf (abs_nonneg m)]

def positiveGaussianLogStep (m : ℝ) (f : E × ℝ → ℝ) (x : E) : ℝ :=
  Real.log (∫ y, Real.exp (m*f (x,y)) ∂gaussianReal 0 1) / m

end UniformBounds
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
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_BoundedDerivatives
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
section SmoothRecursion
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def BoundedDerivs (f : E → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
    (∀ x, ‖fderiv ℝ f x‖ ≤ C) ∧ (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ D)

theorem BoundedDerivs.const_mul {f : E → ℝ} (hf : BoundedDerivs f) (m : ℝ) :
    BoundedDerivs (fun x => m*f x) := by
  obtain ⟨hf,C,D,hC,hD,hb,hbb⟩ := hf
  have hd := hf.differentiable (by norm_num)
  have he : fderiv ℝ (fun x => m*f x) = fun x => m • fderiv ℝ f x := by
    funext x
    exact ((hd x).hasFDerivAt.const_mul m).fderiv
  refine ⟨contDiff_const.mul hf, |m| * C, |m| * D,
    mul_nonneg (abs_nonneg _) hC, mul_nonneg (abs_nonneg _) hD, ?_, ?_⟩
  · intro x
    rw [he, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _)
  · intro x
    rw [he]
    change ‖fderiv ℝ (m • fderiv ℝ f) x‖ ≤ |m| * D
    rw [((hf.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) x).hasFDerivAt.const_smul m |>.fderiv]
    exact (ContinuousLinearMap.opNorm_smul_le _ _).trans (by
      rw [Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hbb x) (abs_nonneg _))

theorem BoundedDerivs.exp_smooth_integral {f : E × ℝ → ℝ} (hf : BoundedDerivs f) :
    ContDiff ℝ 2 (fun x => ∫ y, Real.exp (f (x,y)) ∂gaussianReal 0 1) := by
  obtain ⟨hf,C,D,hC,hD,hb,hbb⟩ := hf
  have hg : HasExpGrowth (fun x => Real.exp (f x)) := by
    simpa only [one_mul] using
      exp_mul_growth_of_fderiv_bound f (hf.differentiable (by norm_num)) C hC hb 1
  exact contDiff_two_gaussian_integral_fderiv _ hf.exp hg
    (fderiv_exp_growth f (hf.differentiable (by norm_num)) hg hC hb)
    (fderiv_fderiv_exp_growth f hf hg hC hD hb hbb)

end SmoothRecursion
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
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_LogDerivatives
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
section LogDerivatives
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_fderiv_log (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    (hn : ∀ x, f x ≠ 0) (x : E) :
    fderiv ℝ (fderiv ℝ (fun x => Real.log (f x))) x =
      (f x)⁻¹ • fderiv ℝ (fderiv ℝ f) x +
      (-(f x ^ 2)⁻¹ • fderiv ℝ f x).smulRight (fderiv ℝ f x) := by
  have hd := hf.differentiable (by norm_num)
  have he : fderiv ℝ (fun x => Real.log (f x)) = fun x => (f x)⁻¹ • fderiv ℝ f x := by
    funext x
    exact ((hd x).hasFDerivAt.log (hn x)).fderiv
  rw [he]
  exact (((hasDerivAt_inv (hn x)).comp_hasFDerivAt x (hd x).hasFDerivAt).smul
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x).hasFDerivAt).fderiv

theorem log_boundedDerivs_of_relative_bounds (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    (hp : ∀ x, 0 < f x) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ C * f x)
    (hbb : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ D * f x) :
    BoundedDerivs (fun x => Real.log (f x)) := by
  have hd := hf.differentiable (by norm_num)
  refine ⟨hf.log (fun x => (hp x).ne'), C, D+C*C, hC, by positivity, ?_, ?_⟩
  · intro x
    rw [((hd x).hasFDerivAt.log (hp x).ne').fderiv, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hp x))]
    calc
      _ ≤ (f x)⁻¹ * (C * f x) := mul_le_mul_of_nonneg_left (hb x) (inv_nonneg.mpr (hp x).le)
      _ = C := by field_simp [(hp x).ne']
  · intro x
    have hfx := (hp x).le
    rw [fderiv_fderiv_log f hf (fun x => (hp x).ne') x]
    calc
      _ ≤ ‖(f x)⁻¹ • fderiv ℝ (fderiv ℝ f) x‖+
        ‖(-(f x ^ 2)⁻¹ • fderiv ℝ f x).smulRight (fderiv ℝ f x)‖ :=
          ContinuousLinearMap.opNorm_add_le _ _
      _ ≤ ‖(f x)⁻¹‖*‖fderiv ℝ (fderiv ℝ f) x‖+
          (‖-(f x ^ 2)⁻¹‖*‖fderiv ℝ f x‖)*‖fderiv ℝ f x‖ := by
        rw [ContinuousLinearMap.norm_smulRight_apply]
        gcongr <;> exact ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ ‖(f x)⁻¹‖*(D*f x)+(‖-(f x ^ 2)⁻¹‖*(C*f x))*(C*f x) := by
        gcongr <;> first | positivity | exact hb _ | exact hbb _
      _ = D+C*C := by
        rw [norm_inv, Real.norm_eq_abs, abs_of_pos (hp x), norm_neg, norm_inv, norm_pow,
          Real.norm_eq_abs, abs_of_pos (hp x)]
        field_simp [(hp x).ne']

theorem norm_fderiv_fderiv_exp_le (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    {C D : ℝ} (hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    (hbb : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ D) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (fun x => Real.exp (f x))) x‖ ≤
      (D+C*C)*Real.exp (f x) := by
  rw [fderiv_fderiv_exp f hf x]
  calc
    _ ≤ ‖Real.exp (f x) • fderiv ℝ (fderiv ℝ f) x‖+
        ‖(Real.exp (f x) • fderiv ℝ f x).smulRight (fderiv ℝ f x)‖ :=
      ContinuousLinearMap.opNorm_add_le _ _
    _ ≤ ‖Real.exp (f x)‖*‖fderiv ℝ (fderiv ℝ f) x‖+
        (‖Real.exp (f x)‖*‖fderiv ℝ f x‖)*‖fderiv ℝ f x‖ := by
      rw [ContinuousLinearMap.norm_smulRight_apply]
      gcongr <;> exact ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ ‖Real.exp (f x)‖*D+(‖Real.exp (f x)‖*C)*C := by gcongr <;> first | exact hb _ | exact hbb _
    _ = _ := by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; ring

end LogDerivatives
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

theorem ParamExpGrowth.smulRight {f : P × E → F →L[ℝ] ℝ} {g : P × E → G}
    (hf : ParamExpGrowth f) (hg : ParamExpGrowth g) :
    ParamExpGrowth (fun z => (f z).smulRight (g z)) := by
  apply (hf.norm.mul hg.norm).of_norm_le zero_le_one
  intro z
  rw [one_mul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (norm_nonneg _),abs_of_nonneg (norm_nonneg _)]
  exact le_of_eq (ContinuousLinearMap.norm_smulRight_apply _ _)

omit [NormedSpace ℝ F] in
theorem ParamExpGrowth.neg {f : P × E → F} (hf : ParamExpGrowth f) :
    ParamExpGrowth (fun z => -f z) := by
  apply hf.of_norm_le zero_le_one
  intro z
  simp

theorem param_fderiv_exp_growth (f : X → ℝ) (ι : P × E → X) (hf : Differentiable ℝ f)
    (hg : ParamExpGrowth (fun z => Real.exp (f (ι z))))
    (hg₁ : ParamExpGrowth (fun z => fderiv ℝ f (ι z))) :
    ParamExpGrowth (fun z => fderiv ℝ (fun x => Real.exp (f x)) (ι z)) := by
  have H := hg.smul hg₁
  simpa only [funext (fun x => ((hf x).hasFDerivAt.exp).fderiv)] using H

theorem param_second_exp_growth (f : X → ℝ) (ι : P × E → X) (hf : ContDiff ℝ 2 f)
    (hg : ParamExpGrowth (fun z => Real.exp (f (ι z))))
    (hg₁ : ParamExpGrowth (fun z => fderiv ℝ f (ι z)))
    (hg₂ : ParamExpGrowth (fun z => fderiv ℝ (fderiv ℝ f) (ι z))) :
    ParamExpGrowth (fun z => fderiv ℝ (fderiv ℝ (fun x => Real.exp (f x))) (ι z)) := by
  have H := (hg.smul hg₂).add ((hg.smul hg₁).smulRight hg₁)
  simpa only [fderiv_fderiv_exp f hf] using H

theorem param_fderiv_log_growth (f : X → ℝ) (ι : P × E → X) (hf : Differentiable ℝ f)
    (hp : ∀ x, f x ≠ 0) (hg : ParamExpGrowth (fun z => (f (ι z))⁻¹))
    (hg₁ : ParamExpGrowth (fun z => fderiv ℝ f (ι z))) :
    ParamExpGrowth (fun z => fderiv ℝ (fun x => Real.log (f x)) (ι z)) := by
  have H := hg.smul hg₁
  have he : fderiv ℝ (fun x => Real.log (f x)) = fun x => (f x)⁻¹ • fderiv ℝ f x :=
    funext (fun x => ((hf x).hasFDerivAt.log (hp x)).fderiv)
  simpa only [he] using H

end ParameterDerivatives
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_ParameterComposition
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
section ParameterComposition
variable {P E X Y : Type} [NormedAddCommGroup P] [NormedAddCommGroup E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem param_fderiv_compCLM_growth (f : Y → ℝ) (L : X →L[ℝ] Y) (ι : P × E → X)
    (hf : Differentiable ℝ f)
    (h : ParamExpGrowth (fun z => fderiv ℝ f (L (ι z)))) :
    ParamExpGrowth (fun z => fderiv ℝ (fun x => f (L x)) (ι z)) := by
  apply h.of_norm_le (norm_nonneg L)
  intro z
  have he : fderiv ℝ (fun x => f (L x)) (ι z) = (fderiv ℝ f (L (ι z))).comp L :=
    ((hf (L (ι z))).hasFDerivAt.comp (ι z) L.hasFDerivAt).fderiv
  rw [he]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq (mul_comm _ _)

theorem param_second_compCLM_growth (f : Y → ℝ) (L : X →L[ℝ] Y) (ι : P × E → X)
    (hf : ContDiff ℝ 2 f)
    (h : ParamExpGrowth (fun z => fderiv ℝ (fderiv ℝ f) (L (ι z)))) :
    ParamExpGrowth (fun z => fderiv ℝ (fderiv ℝ (fun x => f (L x))) (ι z)) := by
  let A : (Y →L[ℝ] ℝ) →L[ℝ] X →L[ℝ] ℝ := (ContinuousLinearMap.compL ℝ X Y ℝ).flip L
  have hA (B : Y →L[ℝ] ℝ) : A B = B.comp L := rfl
  have hAn : ‖A‖ ≤ ‖L‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro B
    rw [hA]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq (mul_comm _ _)
  have hd := hf.differentiable (by norm_num)
  have hdd := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have heq : fderiv ℝ (fun x => f (L x)) = fun x => A (fderiv ℝ f (L x)) := by
    funext x
    exact ((hd (L x)).hasFDerivAt.comp x L.hasFDerivAt).fderiv
  apply h.of_norm_le (mul_nonneg (norm_nonneg L) (norm_nonneg L))
  intro z
  have hsec := A.hasFDerivAt.comp (ι z)
    ((hdd (L (ι z))).hasFDerivAt.comp (ι z) L.hasFDerivAt)
  change HasFDerivAt (fun x => A (fderiv ℝ f (L x)))
    (A.comp ((fderiv ℝ (fderiv ℝ f) (L (ι z))).comp L)) (ι z) at hsec
  rw [heq,hsec.fderiv]
  calc
    _ ≤ ‖A‖*‖(fderiv ℝ (fderiv ℝ f) (L (ι z))).comp L‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖L‖*(‖fderiv ℝ (fderiv ℝ f) (L (ι z))‖*‖L‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ = _ := by ring
end ParameterComposition
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_ParameterWeakGrowth
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
section ParameterWeakGrowth
variable {P E F : Type} [NormedAddCommGroup P] [NormedAddCommGroup E] [Norm F]

theorem ParamExpGrowth.weakNorm {f : P × E → F} (hf : ParamExpGrowth f)
    (hn : ∀ z, 0 ≤ ‖f z‖) : ParamExpGrowth (fun z => ‖f z‖) := by
  apply hf.of_norm_le zero_le_one
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (hn z),one_mul]

theorem ParamExpGrowth.weakLocallyDominated {f : P × (E × ℝ) → F}
    (hf : ParamExpGrowth f) :
    GaussianLocallyDominated (fun z : (P × E) × ℝ => f (z.1.1,(z.1.2,z.2))) := by
  intro R
  obtain ⟨C,M,hC,hM,hf⟩ := hf R
  refine ⟨fun y => C*Real.exp (M*R)*Real.exp (M*|y|),
    (integrable_exp_mul_abs_gaussian M).const_mul _,?_⟩
  rintro ⟨p,e⟩ y hpe
  have hp : ‖p‖ ≤ R := (le_max_left _ _).trans hpe
  have he : ‖e‖ ≤ R := (le_max_right _ _).trans hpe
  apply (hf p (e,y) hp).trans
  change C*Real.exp (M*‖(e,y)‖) ≤ C*Real.exp (M*R)*Real.exp (M*|y|)
  rw [mul_assoc,← Real.exp_add,← mul_add]
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.2
  apply mul_le_mul_of_nonneg_left _ hM
  rw [Prod.norm_def,Real.norm_eq_abs]
  exact max_le (he.trans (le_add_of_nonneg_right (abs_nonneg _)))
    (le_add_of_nonneg_left ((norm_nonneg e).trans he))
end ParameterWeakGrowth
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_LocalMarginal
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
section LocalMarginalDerivatives
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_local_gaussian_integral (f : E × ℝ → F) (hf : ContDiff ℝ 1 f)
    (hg : GaussianLocallyDominated f) (hg₁ : GaussianLocallyDominated (fderiv ℝ f)) (x : E) :
    fderiv ℝ (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) x =
      ∫ y, leftRestrict (fderiv ℝ f (x,y)) ∂gaussianReal 0 1 := by
  exact (hasFDerivAt_local_gaussian_integral f _ hf.continuous
    (leftRestrict.continuous.comp ((hf.fderiv_right (m := 0) (by norm_num)).continuous))
    hg (hg₁.clm leftRestrict)
    (leftRestrict_hasFDerivAt f (hf.differentiable (by norm_num))) x).fderiv

theorem norm_fderiv_local_gaussian_integral_le (f : E × ℝ → F) (hf : ContDiff ℝ 1 f)
    (hg : GaussianLocallyDominated f) (hg₁ : GaussianLocallyDominated (fderiv ℝ f)) (x : E) :
    ‖fderiv ℝ (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) x‖ ≤
      ∫ y, ‖fderiv ℝ f (x,y)‖ ∂gaussianReal 0 1 := by
  rw [fderiv_local_gaussian_integral f hf hg hg₁ x]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono
  · exact ((hg₁.clm leftRestrict).integrable_section
      (leftRestrict.continuous.comp ((hf.fderiv_right (m := 0) (by norm_num)).continuous)) x).norm
  · exact (hg₁.integrable_section ((hf.fderiv_right (m := 0) (by norm_num)).continuous) x).norm
  · exact fun y => leftRestrict_apply_bound _

end LocalMarginalDerivatives
section LocalSecondMarginal
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem secondLeftRestrict_local_growth {f : E × ℝ → ((E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ)}
    (hg : GaussianLocallyDominated f) : GaussianLocallyDominated (fun x => secondLeftRestrict (f x)) := by
  exact hg.of_norm_le zero_le_one (fun point =>
    (secondLeftRestrict_apply_bound (f point)).trans_eq (one_mul _).symm)

theorem fderiv_fderiv_local_gaussian_integral (f : E × ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hg : GaussianLocallyDominated f) (hg₁ : GaussianLocallyDominated (fderiv ℝ f))
    (hg₂ : GaussianLocallyDominated (fderiv ℝ (fderiv ℝ f))) (x : E) :
    fderiv ℝ (fderiv ℝ (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1)) x =
      ∫ y, secondLeftRestrict (fderiv ℝ (fderiv ℝ f) (x,y)) ∂gaussianReal 0 1 := by
  have he : fderiv ℝ (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) =
      fun x => ∫ y, leftRestrict (fderiv ℝ f (x,y)) ∂gaussianReal 0 1 := by
    funext x
    exact fderiv_local_gaussian_integral f (hf.of_le (by norm_num)) hg hg₁ x
  rw [he]
  let T : ((E × ℝ) →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ := leftRestrict
  have hd : ∀ a b, HasFDerivAt (fun z => T (fderiv ℝ f (z,b)))
      (secondLeftRestrict (fderiv ℝ (fderiv ℝ f) (a,b))) a := by
    intro a b
    have h₁ := T.hasFDerivAt.comp (a,b)
      ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) (a,b)).hasFDerivAt
    have hxy : HasFDerivAt (fun z : E => (z,b)) (ContinuousLinearMap.inl ℝ E ℝ) a :=
      (hasFDerivAt_id a).prodMk (hasFDerivAt_const b a)
    convert! h₁.comp a hxy using 1
    all_goals try with_reducible_and_instances rfl
  apply (hasFDerivAt_local_gaussian_integral (fun z => T (fderiv ℝ f z)) _
    (T.continuous.comp (hf.fderiv_right (m := 1) (by norm_num)).continuous)
    (secondLeftRestrict.continuous.comp (hf.fderiv_right (m := 1) (by norm_num)
      |>.fderiv_right (m := 0) (by norm_num)).continuous)
    (hg₁.clm T) (secondLeftRestrict_local_growth hg₂) hd x).fderiv

theorem norm_fderiv_fderiv_local_gaussian_integral_le (f : E × ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hg : GaussianLocallyDominated f) (hg₁ : GaussianLocallyDominated (fderiv ℝ f))
    (hg₂ : GaussianLocallyDominated (fderiv ℝ (fderiv ℝ f))) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1)) x‖ ≤
      ∫ y, ‖fderiv ℝ (fderiv ℝ f) (x,y)‖ ∂gaussianReal 0 1 := by
  rw [fderiv_fderiv_local_gaussian_integral f hf hg hg₁ hg₂ x]
  apply (norm_integral_le_integral_norm _).trans
  have hc := (hf.fderiv_right (m := 1) (by norm_num) |>.fderiv_right (m := 0) (by norm_num)).continuous
  apply integral_mono_of_nonneg (ae_of_all _ (fun y =>
    ContinuousLinearMap.opNorm_nonneg (secondLeftRestrict (fderiv ℝ (fderiv ℝ f) (x,y)))))
  · exact (hg₂.integrable_section hc x).norm
  · exact ae_of_all _ (fun y => secondLeftRestrict_apply_bound _)

end LocalSecondMarginal
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_ParameterIntegral
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
section ParameterIntegral
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem param_contDiff_gaussian_integral (f : (P × E) × ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hg : ParamExpGrowth (fun z : P × (E × ℝ) => f ((z.1,z.2.1),z.2.2)))
    (hg₁ : ParamExpGrowth (fun z : P × (E × ℝ) => fderiv ℝ f ((z.1,z.2.1),z.2.2)))
    (hg₂ : ParamExpGrowth (fun z : P × (E × ℝ) => fderiv ℝ (fderiv ℝ f) ((z.1,z.2.1),z.2.2))) :
    ContDiff ℝ 2 (fun z => ∫ y, f (z,y) ∂gaussianReal 0 1) := by
  exact contDiff_two_local_gaussian_integral_fderiv f hf hg.weakLocallyDominated
    hg₁.weakLocallyDominated hg₂.weakLocallyDominated

theorem param_fderiv_gaussian_integral_growth (f : (P × E) × ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hg : ParamExpGrowth (fun z : P × (E × ℝ) => f ((z.1,z.2.1),z.2.2)))
    (hg₁ : ParamExpGrowth (fun z : P × (E × ℝ) => fderiv ℝ f ((z.1,z.2.1),z.2.2))) :
    ParamExpGrowth (fderiv ℝ (fun z => ∫ y, f (z,y) ∂gaussianReal 0 1)) := by
  have H : ParamExpGrowth (fun z : P × E => ∫ y, ‖fderiv ℝ f (z,y)‖ ∂gaussianReal 0 1) :=
    (hg₁.weakNorm (fun _ => ContinuousLinearMap.opNorm_nonneg _)).gaussian_integral
  apply H.of_norm_le zero_le_one
  intro z
  rw [one_mul,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun y => ContinuousLinearMap.opNorm_nonneg (fderiv ℝ f (z,y))))]
  exact norm_fderiv_local_gaussian_integral_le f hf hg.weakLocallyDominated hg₁.weakLocallyDominated z

theorem param_second_gaussian_integral_growth (f : (P × E) × ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hg : ParamExpGrowth (fun z : P × (E × ℝ) => f ((z.1,z.2.1),z.2.2)))
    (hg₁ : ParamExpGrowth (fun z : P × (E × ℝ) => fderiv ℝ f ((z.1,z.2.1),z.2.2)))
    (hg₂ : ParamExpGrowth (fun z : P × (E × ℝ) => fderiv ℝ (fderiv ℝ f) ((z.1,z.2.1),z.2.2))) :
    ParamExpGrowth (fderiv ℝ (fderiv ℝ (fun z => ∫ y, f (z,y) ∂gaussianReal 0 1))) := by
  have H : ParamExpGrowth (fun z : P × E => ∫ y, ‖fderiv ℝ (fderiv ℝ f) (z,y)‖ ∂gaussianReal 0 1) :=
    (hg₂.weakNorm (fun _ => ContinuousLinearMap.opNorm_nonneg _)).gaussian_integral
  apply H.of_norm_le zero_le_one
  intro z
  rw [one_mul,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun y => ContinuousLinearMap.opNorm_nonneg (fderiv ℝ (fderiv ℝ f) (z,y))))]
  exact norm_fderiv_fderiv_local_gaussian_integral_le f hf hg.weakLocallyDominated
    hg₁.weakLocallyDominated hg₂.weakLocallyDominated z
end ParameterIntegral
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_ParameterLinear
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
section ParameterLinear
variable {P E : Type} [NormedAddCommGroup P] [NormedAddCommGroup E]

theorem ParamLinearGrowth.const_mul {f : P × E → ℝ} (hf : ParamLinearGrowth f) (m : ℝ) :
    ParamLinearGrowth (fun z => m*f z) := by
  intro R
  obtain ⟨C,hC,hf⟩ := hf R
  refine ⟨|m| *C,mul_nonneg (abs_nonneg _) hC,?_⟩
  intro p e hp
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left (hf p e hp) (abs_nonneg _)).trans_eq (mul_assoc _ _ _).symm

theorem ParamLinearGrowth.gaussian_integral {f : P × (E × ℝ) → ℝ}
    (hf : ParamLinearGrowth f) :
    ParamLinearGrowth (fun z : P × E => ∫ y, f (z.1,(z.2,y)) ∂gaussianReal 0 1) := by
  intro R
  obtain ⟨C,hC,hf⟩ := hf R
  let B := ∫ y : ℝ, Real.exp |y| ∂gaussianReal 0 1
  have hB : 0 ≤ B := integral_nonneg (fun _ => (Real.exp_pos _).le)
  have hI : Integrable (fun y : ℝ => Real.exp |y|) (gaussianReal 0 1) := by
    simpa only [one_mul] using integrable_exp_mul_abs_gaussian 1
  refine ⟨C*B,mul_nonneg hC hB,?_⟩
  intro p e hp
  have hh y : |f (p,(e,y))| ≤ C*(1+‖e‖)*Real.exp |y| := by
    apply (hf p (e,y) hp).trans
    rw [Prod.norm_def,Real.norm_eq_abs]
    have hmax := max_le_add_of_nonneg (norm_nonneg e) (abs_nonneg y)
    have hex := Real.add_one_le_exp |y|
    have hprod := mul_nonneg (norm_nonneg e) (abs_nonneg y)
    have H : 1+max ‖e‖ |y| ≤ (1+‖e‖)*Real.exp |y| := by
      calc
        _ ≤ (1+‖e‖)*(1+|y|) := by nlinarith
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact (mul_le_mul_of_nonneg_left H hC).trans_eq (mul_assoc _ _ _).symm
  calc
    _ = ‖∫ y, f (p,(e,y)) ∂gaussianReal 0 1‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ y, ‖f (p,(e,y))‖ ∂gaussianReal 0 1 := norm_integral_le_integral_norm _
    _ ≤ ∫ y, C*(1+‖e‖)*Real.exp |y| ∂gaussianReal 0 1 :=
      integral_mono_of_nonneg (ae_of_all _ (fun _ => norm_nonneg _)) (hI.const_mul _)
        (ae_of_all _ hh)
    _ = _ := by rw [integral_const_mul]; dsimp [B]; ring
end ParameterLinear

theorem gaussian_exp_integral_bounds (g : ℝ → ℝ) (hg : Continuous g) {A C : ℝ}
    (_hC : 0 ≤ C) (hb : ∀ y, |g y| ≤ A+C*|y|) :
    let Z := ∫ y, Real.exp (g y) ∂gaussianReal 0 1
    Real.exp (-A)*(∫ y : ℝ, Real.exp (-C*|y|) ∂gaussianReal 0 1) ≤ Z ∧
    Z ≤ Real.exp A*(∫ y : ℝ, Real.exp (C*|y|) ∂gaussianReal 0 1) := by
  have hupper y : Real.exp (g y) ≤ Real.exp A*Real.exp (C*|y|) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 ((le_abs_self _).trans (hb y))
  have hlower y : Real.exp (-A)*Real.exp (-C*|y|) ≤ Real.exp (g y) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have hh := (abs_le.1 (hb y)).1
    linarith
  have hI : Integrable (fun y => Real.exp (g y)) (gaussianReal 0 1) := by
    apply ((integrable_exp_mul_abs_gaussian C).const_mul (Real.exp A)).mono' (Real.continuous_exp.comp hg).aestronglyMeasurable
    exact ae_of_all _ (fun y => by simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hupper y)
  dsimp only
  constructor
  · rw [← integral_const_mul]
    exact integral_mono ((integrable_exp_mul_abs_gaussian (-C)).const_mul _) hI hlower
  · rw [← integral_const_mul]
    exact integral_mono hI ((integrable_exp_mul_abs_gaussian C).const_mul _) hupper

section LogParameterLinear
variable {P E : Type} [NormedAddCommGroup P] [NormedAddCommGroup E]

theorem ParamLinearGrowth.log_gaussian_exp {f : P × (E × ℝ) → ℝ}
    (hf : ParamLinearGrowth f) (hc : Continuous f) :
    ParamLinearGrowth (fun z : P × E => Real.log (∫ y, Real.exp (f (z.1,(z.2,y))) ∂gaussianReal 0 1)) := by
  intro R
  obtain ⟨C,hC,hf⟩ := hf R
  let Bp := ∫ y : ℝ, Real.exp (C*|y|) ∂gaussianReal 0 1
  let Bm := ∫ y : ℝ, Real.exp (-C*|y|) ∂gaussianReal 0 1
  have hp : 0 < Bp := integral_exp_pos (integrable_exp_mul_abs_gaussian C)
  have hm : 0 < Bm := integral_exp_pos (integrable_exp_mul_abs_gaussian (-C))
  let D := C+|Real.log Bp|+|Real.log Bm|
  refine ⟨D,by dsimp [D]; positivity,?_⟩
  intro p e he
  let A := C*(1+‖e‖)
  have hb y : |f (p,(e,y))| ≤ A+C*|y| := by
    apply (hf p (e,y) he).trans
    rw [Prod.norm_def,Real.norm_eq_abs]
    have hh := max_le_add_of_nonneg (norm_nonneg e) (abs_nonneg y)
    dsimp [A]
    nlinarith
  have H := gaussian_exp_integral_bounds (fun y => f (p,(e,y)))
    (hc.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))) hC hb
  let Z := ∫ y, Real.exp (f (p,(e,y))) ∂gaussianReal 0 1
  have hz : 0 < Z := lt_of_lt_of_le (mul_pos (Real.exp_pos _) hm) H.1
  have hu := Real.log_le_log hz H.2
  have hl := Real.log_le_log (mul_pos (Real.exp_pos _) hm) H.1
  change Real.log Z ≤ Real.log (Real.exp A*Bp) at hu
  change Real.log (Real.exp (-A)*Bm) ≤ Real.log Z at hl
  rw [Real.log_mul (Real.exp_pos _).ne' hp.ne',Real.log_exp] at hu
  rw [Real.log_mul (Real.exp_pos _).ne' hm.ne',Real.log_exp] at hl
  change |Real.log Z| ≤ D*(1+‖e‖)
  apply abs_le.2
  constructor
  · have hh := le_abs_self (Real.log Bm)
    have hneg := neg_abs_le (Real.log Bm)
    have hextra := mul_nonneg (add_nonneg (abs_nonneg (Real.log Bp)) (abs_nonneg (Real.log Bm))) (norm_nonneg e)
    dsimp [A,D] at *
    linarith [abs_nonneg (Real.log Bp)]
  · have hh := le_abs_self (Real.log Bp)
    have hextra := mul_nonneg (add_nonneg (abs_nonneg (Real.log Bp)) (abs_nonneg (Real.log Bm))) (norm_nonneg e)
    dsimp [A,D] at *
    linarith [abs_nonneg (Real.log Bm)]
end LogParameterLinear
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyRegularity
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
section ClosedHierarchy
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BoundedDerivs.log_gaussian_integral_exp {f : E × ℝ → ℝ} (h : BoundedDerivs f) :
    BoundedDerivs (fun x => Real.log (∫ y, Real.exp (f (x,y)) ∂gaussianReal 0 1)) := by
  obtain ⟨hf,C,D,hC,hD,hb,hbb⟩ := h
  have hd := hf.differentiable (by norm_num)
  have hg : HasExpGrowth (fun x => Real.exp (f x)) := by
    simpa only [one_mul] using exp_mul_growth_of_fderiv_bound f hd C hC hb 1
  have hg₁ := fderiv_exp_growth f hd hg hC hb
  have hg₂ := fderiv_fderiv_exp_growth f hf hg hC hD hb hbb
  have hp : ∀ x, 0 < ∫ y, Real.exp (f (x,y)) ∂gaussianReal 0 1 := by
    intro x
    apply integral_exp_pos
    exact hg.integrable_gaussian_section hf.exp.continuous x
  apply log_boundedDerivs_of_relative_bounds _
    (BoundedDerivs.exp_smooth_integral ⟨hf,C,D,hC,hD,hb,hbb⟩) hp hC
    (show 0 ≤ D+C*C by positivity)
  · intro x
    apply (norm_fderiv_gaussian_integral_le _ (hf.exp.of_le (by norm_num)) hg hg₁ x).trans
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg (ae_of_all _ (fun y =>
      ContinuousLinearMap.opNorm_nonneg (fderiv ℝ (fun z => Real.exp (f z)) (x,y))))
    · exact (hg.integrable_gaussian_section hf.exp.continuous x).const_mul C
    · apply ae_of_all
      intro y
      dsimp only
      rw [fderiv_exp (hd (x,y)), norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact (mul_le_mul_of_nonneg_left (hb (x,y)) (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  · intro x
    apply (norm_fderiv_fderiv_gaussian_integral_le _ hf.exp hg hg₁ hg₂ x).trans
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg (ae_of_all _ (fun y =>
      ContinuousLinearMap.opNorm_nonneg (fderiv ℝ (fderiv ℝ (fun z => Real.exp (f z))) (x,y))))
    · exact (hg.integrable_gaussian_section hf.exp.continuous x).const_mul (D+C*C)
    · exact ae_of_all _ (fun y => norm_fderiv_fderiv_exp_le f hf hC hD hb hbb (x,y))

theorem BoundedDerivs.positiveGaussianLogStep {f : E × ℝ → ℝ} (h : BoundedDerivs f) (m : ℝ) :
    BoundedDerivs (positiveGaussianLogStep m f) := by
  have hh := ((h.const_mul m).log_gaussian_integral_exp).const_mul m⁻¹
  change BoundedDerivs (fun x => Real.log
    (∫ y, Real.exp (m*f (x,y)) ∂gaussianReal 0 1) / m)
  simpa only [div_eq_mul_inv, mul_comm] using hh

end ClosedHierarchy
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

theorem growth_of_fderiv_bound (f : E → ℝ) (hd : Differentiable ℝ f)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ C) : HasExpGrowth f := by
  refine ⟨‖f 0‖+C,1,add_nonneg (norm_nonneg _) hC,zero_le_one,?_⟩
  intro x
  rw [one_mul]
  apply (norm_le_of_fderiv_bound f hd C hb x).trans
  have he₀ : 1 ≤ Real.exp ‖x‖ := Real.one_le_exp (norm_nonneg _)
  have he₁ : ‖x‖ ≤ Real.exp ‖x‖ := (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  calc
    ‖f 0‖+C*‖x‖ ≤ ‖f 0‖*Real.exp ‖x‖ + C*Real.exp ‖x‖ := by
      gcongr
      exact (le_mul_of_one_le_right (norm_nonneg _) he₀)
    _ = _ := by ring

theorem BoundedDerivs.gaussian_integral {f : E × ℝ → ℝ} (h : BoundedDerivs f) :
    BoundedDerivs (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) := by
  obtain ⟨hf,C,D,hC,hD,hb,hbb⟩ := h
  have hg := growth_of_fderiv_bound f (hf.differentiable (by norm_num)) hC hb
  have hg₁ := HasExpGrowth.of_bounded hC hb
  have hg₂ := HasExpGrowth.of_bounded hD hbb
  refine ⟨contDiff_two_gaussian_integral_fderiv f hf hg hg₁ hg₂,C,D,hC,hD,?_,?_⟩
  · intro x
    apply (norm_fderiv_gaussian_integral_le f (hf.of_le (by norm_num)) hg hg₁ x).trans
    calc
      _ ≤ ∫ _, C ∂gaussianReal 0 1 := by
        apply integral_mono_of_nonneg (ae_of_all _ (fun y => norm_nonneg _)) (integrable_const _)
        exact ae_of_all _ (fun y => hb (x,y))
      _ = C := by simp
  · intro x
    apply (norm_fderiv_fderiv_gaussian_integral_le f hf hg hg₁ hg₂ x).trans
    calc
      _ ≤ ∫ _, D ∂gaussianReal 0 1 := by
        apply integral_mono_of_nonneg
          (ae_of_all _ (fun y => ContinuousLinearMap.opNorm_nonneg (fderiv ℝ (fderiv ℝ f) (x,y))))
          (integrable_const _)
        exact ae_of_all _ (fun y => hbb (x,y))
      _ = D := by simp

def gaussianStep (m : ℝ) (f : E × ℝ → ℝ) (x : E) : ℝ :=
  if m = 0 then ∫ y, f (x,y) ∂gaussianReal 0 1 else positiveGaussianLogStep m f x

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

def gaussianStepLaw (m : ℝ) (f : E × ℝ → ℝ) (x : E) : Measure ℝ :=
  (gaussianReal 0 1).tilted (fun y => m*f (x,y))

theorem BoundedDerivs.exp_integrable {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (m : ℝ) (x : E) : Integrable (fun y => Real.exp (m*f (x,y))) (gaussianReal 0 1) := by
  obtain ⟨hf,C,D,hC,hD,hb,hbb⟩ := hf
  exact (exp_mul_growth_of_fderiv_bound f (hf.differentiable (by norm_num)) C hC hb m).integrable_gaussian_section (Real.continuous_exp.comp (continuous_const.mul hf.continuous)) x

theorem BoundedDerivs.gaussianStep {f : E × ℝ → ℝ} (hf : BoundedDerivs f) (m : ℝ) :
    BoundedDerivs (gaussianStep m f) := by
  unfold SK.Analytic.gaussianStep
  split
  · exact hf.gaussian_integral
  · exact hf.positiveGaussianLogStep m

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

theorem fderiv_fderiv_const_mul (f : E → ℝ) (hf : ContDiff ℝ 2 f) (c : ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ (fun z => c*f z)) x = c • fderiv ℝ (fderiv ℝ f) x := by
  have he : fderiv ℝ (fun z => c*f z) = fun z => c • fderiv ℝ f z := by
    funext z
    exact ((hf.differentiable (by norm_num) z).hasFDerivAt.const_mul c).fderiv
  rw [he]
  exact (((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x).hasFDerivAt.const_smul c).fderiv

theorem BoundedDerivs.exp_growths {f : E → ℝ} (hf : BoundedDerivs f) (m : ℝ) :
    HasExpGrowth (fun x => Real.exp (m*f x)) ∧
    HasExpGrowth (fderiv ℝ (fun x => Real.exp (m*f x))) ∧
    HasExpGrowth (fderiv ℝ (fderiv ℝ (fun x => Real.exp (m*f x)))) := by
  obtain ⟨hfd,C,D,hC,hD,hb,hbb⟩ := hf.const_mul m
  have hg : HasExpGrowth (fun x => Real.exp (m*f x)) := by
    simpa only [one_mul] using exp_mul_growth_of_fderiv_bound (fun x => m*f x)
      (hfd.differentiable (by norm_num)) C hC hb 1
  exact ⟨hg,fderiv_exp_growth _ (hfd.differentiable (by norm_num)) hg hC hb,
    fderiv_fderiv_exp_growth _ hfd hg hC hD hb hbb⟩

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

def ParamRegular (f : P × E → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ ParamLinearGrowth f ∧ ParamExpGrowth (fderiv ℝ f) ∧
    ParamExpGrowth (fderiv ℝ (fderiv ℝ f))

theorem ParamRegular.const_mul {f : P × E → ℝ} (hf : ParamRegular f) (c : ℝ) :
    ParamRegular (fun z => c*f z) := by
  refine ⟨contDiff_const.mul hf.1,hf.2.1.const_mul c,?_,?_⟩
  · apply hf.2.2.1.of_norm_le (abs_nonneg c)
    intro z
    rw [((hf.1.differentiable (by norm_num) z).hasFDerivAt.const_mul c).fderiv]
    simp only [norm_smul,Real.norm_eq_abs]
    exact le_rfl
  · apply hf.2.2.2.of_norm_le (abs_nonneg c)
    intro z
    rw [fderiv_fderiv_const_mul f hf.1 c]
    simpa only [Real.norm_eq_abs] using ContinuousLinearMap.opNorm_smul_le c (fderiv ℝ (fderiv ℝ f) z)

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
theorem ParamExpGrowth.weakAdd {P E F : Type} [NormedAddCommGroup P]
    [NormedAddCommGroup E] [Norm F] [Add F] {f g : P × E → F}
    (hf : ParamExpGrowth f) (hg : ParamExpGrowth g)
    (hadd : ∀ z, ‖f z+g z‖ ≤ ‖f z‖+‖g z‖) : ParamExpGrowth (fun z => f z+g z) := by
  intro R
  obtain ⟨C,M,hC,hM,hf⟩ := hf R
  obtain ⟨D,L,hD,hL,hg⟩ := hg R
  refine ⟨C+D,max M L,add_nonneg hC hD,(le_max_left M L).trans' hM,?_⟩
  intro p e hp
  calc
    _ ≤ ‖f (p,e)‖+‖g (p,e)‖ := hadd (p,e)
    _ ≤ C*Real.exp (M*‖e‖)+D*Real.exp (L*‖e‖) := add_le_add (hf p e hp) (hg p e hp)
    _ ≤ C*Real.exp (max M L*‖e‖)+D*Real.exp (max M L*‖e‖) := by
      gcongr <;> first | exact le_max_left _ _ | exact le_max_right _ _
    _ = _ := by ring

section ParameterAlgebra
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def ParamSmooth (f : P × E → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ ParamExpGrowth f ∧ ParamExpGrowth (fderiv ℝ f) ∧
    ParamExpGrowth (fderiv ℝ (fderiv ℝ f))

theorem ParamSmooth.add {f g : P × E → ℝ} (hf : ParamSmooth f) (hg : ParamSmooth g) :
    ParamSmooth (fun z => f z+g z) := by
  have he : fderiv ℝ (fun z => f z+g z) = fun z => fderiv ℝ f z+fderiv ℝ g z := by
    funext z
    exact ((hf.1.differentiable (by norm_num) z).hasFDerivAt.fun_add
      (hg.1.differentiable (by norm_num) z).hasFDerivAt).fderiv
  have he₂ : fderiv ℝ (fderiv ℝ (fun z => f z+g z)) =
      fun z => fderiv ℝ (fderiv ℝ f) z+fderiv ℝ (fderiv ℝ g) z := by
    rw [he]
    funext z
    exact (((hf.1.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) z).hasFDerivAt.fun_add
      ((hg.1.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) z).hasFDerivAt).fderiv
  refine ⟨hf.1.add hg.1,hf.2.1.add hg.2.1,?_,?_⟩
  · rw [he]
    exact hf.2.2.1.add hg.2.2.1
  · rw [he₂]
    exact hf.2.2.2.weakAdd hg.2.2.2 (fun _ => ContinuousLinearMap.opNorm_add_le _ _)

theorem ParamRegular.toSmooth {f : P × E → ℝ} (hf : ParamRegular f) : ParamSmooth f :=
  ⟨hf.1,hf.2.1.expGrowth,hf.2.2⟩

theorem ParamRegular.expSmooth {f : P × E → ℝ} (hf : ParamRegular f) :
    ParamSmooth (fun z => Real.exp (f z)) := by
  have hg : ParamExpGrowth (fun z => Real.exp (f z)) := by
    simpa only [one_mul] using hf.2.1.exp_mul 1
  exact ⟨hf.1.exp,hg,
    param_fderiv_exp_growth f id (hf.1.differentiable (by norm_num)) hg hf.2.2.1,
    param_second_exp_growth f id hf.1 hg hf.2.2.1 hf.2.2.2⟩

omit [NormedSpace ℝ P] [NormedSpace ℝ E] in
theorem ParamLinearGrowth.add {f g : P × E → ℝ} (hf : ParamLinearGrowth f)
    (hg : ParamLinearGrowth g) : ParamLinearGrowth (fun z => f z+g z) := by
  intro R
  obtain ⟨C,hC,hf⟩ := hf R
  obtain ⟨D,hD,hg⟩ := hg R
  refine ⟨C+D,add_nonneg hC hD,?_⟩
  intro p e hp
  exact (abs_add_le _ _).trans ((add_le_add (hf p e hp) (hg p e hp)).trans_eq (add_mul _ _ _).symm)

theorem ParamRegular.add {f g : P × E → ℝ} (hf : ParamRegular f) (hg : ParamRegular g) :
    ParamRegular (fun z => f z+g z) := by
  have H := hf.toSmooth.add hg.toSmooth
  exact ⟨H.1,hf.2.1.add hg.2.1,H.2.2⟩

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
theorem ParamExpGrowth.weakSmul {P E F : Type} [NormedAddCommGroup P]
    [NormedAddCommGroup E] [Norm F] [SMul ℝ F] {f : P × E → ℝ} {g : P × E → F}
    (hf : ParamExpGrowth f) (hg : ParamExpGrowth g)
    (hn : ∀ z, 0 ≤ ‖g z‖) (hm : ∀ z, ‖f z • g z‖ ≤ ‖f z‖*‖g z‖) :
    ParamExpGrowth (fun z => f z • g z) := by
  apply (hf.norm.mul (hg.weakNorm hn)).of_norm_le zero_le_one
  intro z
  rw [one_mul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (norm_nonneg (f z)),abs_of_nonneg (hn z)]
  exact hm z

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_ParameterInverse
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
section ParameterInverse
variable {P E : Type} [NormedAddCommGroup P] [NormedAddCommGroup E]

theorem ParamLinearGrowth.inv_gaussian_exp {f : P × (E × ℝ) → ℝ}
    (hf : ParamLinearGrowth f) (hc : Continuous f) :
    ParamExpGrowth (fun z : P × E => (∫ y, Real.exp (f (z.1,(z.2,y))) ∂gaussianReal 0 1)⁻¹) := by
  intro R
  obtain ⟨C,hC,hf⟩ := hf R
  let B := ∫ y : ℝ, Real.exp (-C*|y|) ∂gaussianReal 0 1
  have hB : 0 < B := integral_exp_pos (integrable_exp_mul_abs_gaussian (-C))
  refine ⟨Real.exp C/B,C,by positivity,hC,?_⟩
  intro p e he
  let A := C*(1+‖e‖)
  have hb y : |f (p,(e,y))| ≤ A+C*|y| := by
    apply (hf p (e,y) he).trans
    rw [Prod.norm_def,Real.norm_eq_abs]
    have hh := max_le_add_of_nonneg (norm_nonneg e) (abs_nonneg y)
    dsimp [A]
    nlinarith
  have H := gaussian_exp_integral_bounds (fun y => f (p,(e,y)))
    (hc.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))) hC hb
  let Z := ∫ y, Real.exp (f (p,(e,y))) ∂gaussianReal 0 1
  have hlo : 0 < Real.exp (-A)*B := mul_pos (Real.exp_pos _) hB
  have hz : 0 < Z := hlo.trans_le H.1
  change ‖Z⁻¹‖ ≤ Real.exp C/B*Real.exp (C*‖e‖)
  rw [Real.norm_eq_abs,abs_of_pos (inv_pos.2 hz)]
  calc
    Z⁻¹ ≤ (Real.exp (-A)*B)⁻¹ := (inv_le_inv₀ hz hlo).2 H.1
    _ = Real.exp C/B*Real.exp (C*‖e‖) := by
      rw [mul_inv_rev,Real.exp_neg,inv_inv]
      dsimp [A]
      rw [mul_add,mul_one,Real.exp_add]
      ring
end ParameterInverse
end SK.Analytic

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

theorem ParamRegular.exp_gaussian_pos {f : P × (E × ℝ) → ℝ}
    (hf : ParamRegular f) (m : ℝ) (z : P × E) :
    0 < ∫ y, Real.exp (m*f (z.1,(z.2,y))) ∂gaussianReal 0 1 := by
  apply integral_exp_pos
  exact (hf.2.1.exp_mul m).weakLocallyDominated.integrable_section
    (Real.continuous_exp.comp (continuous_const.mul (hf.1.continuous.comp
      (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))))) z

end ParameterAverage
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_ParameterBilinear
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
section ParameterBilinear
variable {P E F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem ParamExpGrowth.continuousLinearMap (L : P × E →L[ℝ] F) : ParamExpGrowth (fun z => L z) := by
  intro R
  refine ⟨‖L‖*Real.exp (max R 0),1,by positivity,by norm_num,?_⟩
  intro p e hp
  calc
    ‖L (p,e)‖ ≤ ‖L‖*‖(p,e)‖ := L.le_opNorm _
    _ ≤ ‖L‖*Real.exp (‖(p,e)‖) := by
      gcongr
      have hh := Real.add_one_le_exp ‖(p,e)‖
      linarith
    _ ≤ ‖L‖*Real.exp (max R 0+‖e‖) := by
      gcongr
      rw [Prod.norm_def]
      exact max_le ((hp.trans (le_max_left _ _)).trans (le_add_of_nonneg_right (norm_nonneg e)))
        (le_add_of_nonneg_left (le_max_right _ _))
    _ = _ := by rw [Real.exp_add,one_mul,mul_assoc]

end ParameterBilinear
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

omit [NormedSpace ℝ P] in
theorem ParamExpGrowth.fieldComp {F : Type} [Norm F] {f : P × E → F}
    (hf : ParamExpGrowth f) (L : D →L[ℝ] E) :
    ParamExpGrowth (fun z : P × D => f (z.1,L z.2)) := by
  intro R
  obtain ⟨C,M,hC,hM,hf⟩ := hf R
  refine ⟨C,M*‖L‖,hC,mul_nonneg hM (norm_nonneg L),?_⟩
  intro p e hp
  apply (hf p (L e) hp).trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.2
  exact (mul_le_mul_of_nonneg_left (L.le_opNorm e) hM).trans_eq (mul_assoc _ _ _).symm

end ParameterFieldMap
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_FiniteMarkovPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SK.Analytic
namespace FiniteMarkov
variable {X : Type*}

theorem sum_cons [Fintype X] (m : ℕ) (f : (Fin (m+1) → X) → ℝ) :
    (∑ s,f s)=∑ x : X,∑ t : Fin m → X,f (Fin.cons x t) := by
  classical
  calc
    _ = ∑ z : X × (Fin m → X),f (Fin.cons z.1 z.2) := by
      apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m+1) => X)).symm
      intro s
      simp only [Fin.consEquiv_symm_apply,Fin.cons_self_tail]
    _ = _ := Fintype.sum_prod_type _

def walkWeight (K : X → X → ℝ) : (m : ℕ) → X → (Fin m → X) → ℝ
  | 0,_,_ => 1
  | m+1,x,s => K x (s 0)*walkWeight K m (s 0) (Fin.tail s)

@[simp] theorem walkWeight_zero (K : X → X → ℝ) (x : X) (s : Fin 0 → X) :
    walkWeight K 0 x s=1 := rfl

@[simp] theorem walkWeight_cons (K : X → X → ℝ) (m : ℕ) (x y : X) (s : Fin m → X) :
    walkWeight K (m+1) x (Fin.cons y s)=K x y*walkWeight K m y s := rfl

theorem walkWeight_nonneg (K : X → X → ℝ) (hK : ∀ x y,0≤K x y) (m : ℕ) (x : X) (s : Fin m → X) :
    0≤walkWeight K m x s := by
  induction m generalizing x with
  | zero => exact zero_le_one
  | succ m ih => exact mul_nonneg (hK _ _) (ih _ _)

theorem walkWeight_sum [Fintype X] (K : X → X → ℝ) (hK : ∀ x,∑ y,K x y=1) (m : ℕ) (x : X) :
    ∑ s : Fin m → X,walkWeight K m x s=1 := by
  classical
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [sum_cons]
    simp only [walkWeight_cons,← Finset.mul_sum,ih,mul_one,hK]

def pathWeight (p : X → ℝ) (K : X → X → ℝ) (m : ℕ) (s : Fin (m+1) → X) : ℝ :=
  p (s 0)*walkWeight K m (s 0) (Fin.tail s)

theorem pathWeight_nonneg (p : X → ℝ) (K : X → X → ℝ)
    (hp : ∀ x,0≤p x) (hK : ∀ x y,0≤K x y) (m : ℕ) (s : Fin (m+1) → X) :
    0≤pathWeight p K m s := mul_nonneg (hp _) (walkWeight_nonneg K hK _ _ _)

theorem pathWeight_sum [Fintype X] (p : X → ℝ) (K : X → X → ℝ)
    (hp : ∑ x,p x=1) (hK : ∀ x,∑ y,K x y=1) (m : ℕ) :
    ∑ s : Fin (m+1) → X,pathWeight p K m s=1 := by
  rw [sum_cons]
  simp only [pathWeight,Fin.cons_zero,Fin.tail_cons,← Finset.mul_sum,walkWeight_sum K hK,mul_one,hp]

end FiniteMarkov

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_FiniteLaw
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

structure FiniteLaw (X : Type*) [Fintype X] where
  weight : X → ℝ
  nonneg : ∀ x, 0 ≤ weight x
  sum_one : ∑ x, weight x=1

namespace FiniteLaw
variable {X Y : Type*} [Fintype X] [Fintype Y]

def expect (P : FiniteLaw X) (f : X → ℝ) : ℝ := ∑ x, P.weight x*f x

def prob (P : FiniteLaw X) (E : X → Prop) : ℝ := P.expect (fun x => if E x then 1 else 0)

@[simp] theorem expect_const (P : FiniteLaw X) (c : ℝ) : P.expect (fun _ => c)=c := by
  simp only [expect,← Finset.sum_mul,P.sum_one,one_mul]

@[simp] theorem expect_zero (P : FiniteLaw X) : P.expect (fun _ => 0)=0 := expect_const P 0

@[simp] theorem prob_true (P : FiniteLaw X) : P.prob (fun _ => True)=1 := by simp [prob]
@[simp] theorem prob_false (P : FiniteLaw X) : P.prob (fun _ => False)=0 := by simp [prob]

def prod (P : FiniteLaw X) (Q : FiniteLaw Y) : FiniteLaw (X × Y) where
  weight z := P.weight z.1*Q.weight z.2
  nonneg z := mul_nonneg (P.nonneg _) (Q.nonneg _)
  sum_one := by simp only [Fintype.sum_prod_type,← Finset.mul_sum,Q.sum_one,mul_one,P.sum_one]

def pi {I : Type*} [Fintype I] [DecidableEq I] (A : I → Type*) [∀ i, Fintype (A i)] (P : ∀ i, FiniteLaw (A i)) :
    FiniteLaw (∀ i, A i) where
  weight z := ∏ i, (P i).weight (z i)
  nonneg z := Finset.prod_nonneg (fun i _ => (P i).nonneg _)
  sum_one := by rw [← Fintype.prod_sum]; simp only [sum_one,Finset.prod_const_one]

end FiniteLaw

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_FiniteProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical
namespace SK.Analytic.FiniteLaw
variable {X I J : Type*} [Fintype X] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def iid (P : FiniteLaw X) (I : Type*) [Fintype I] [DecidableEq I] : FiniteLaw (I → X) :=
  pi (fun _ : I => X) (fun _ => P)

end SK.Analytic.FiniteLaw

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

abbrev BankIndex {p : ℕ} (K : Fin p → ℕ) := (j : Fin p) × Fin (K j)
abbrev BankPrior {p : ℕ} (pred : Fin p → Finset (Fin p)) (j : Fin p) := {i : Fin p // i∈pred j}
abbrev BankTuple {p : ℕ} (K : Fin p → ℕ) (pred : Fin p → Finset (Fin p)) (j : Fin p) :=
  (i : BankPrior pred j) → Fin (K i.val)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_RegularAlgebra
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
section RegularAlgebra
variable {E D : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem BoundedDerivs.add {f g : E → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g) :
    BoundedDerivs (fun x => f x+g x) := by
  obtain ⟨hf,C,D,hC,hD,hf₁,hf₂⟩ := hf
  obtain ⟨hg,A,B,hA,hB,hg₁,hg₂⟩ := hg
  have hd := hf.differentiable (by norm_num)
  have he := hg.differentiable (by norm_num)
  have heq : fderiv ℝ (fun x => f x+g x) = fun x => fderiv ℝ f x+fderiv ℝ g x := by
    funext x
    exact ((hd x).hasFDerivAt.add (he x).hasFDerivAt).fderiv
  have hdd := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hee := (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  refine ⟨hf.add hg,C+A,D+B,add_nonneg hC hA,add_nonneg hD hB,?_,?_⟩
  · intro x
    rw [heq]
    exact (ContinuousLinearMap.opNorm_add_le _ _).trans (add_le_add (hf₁ x) (hg₁ x))
  · intro x
    rw [heq, ((hdd x).hasFDerivAt.fun_add (hee x).hasFDerivAt).fderiv]
    exact (ContinuousLinearMap.opNorm_add_le _ _).trans (add_le_add (hf₂ x) (hg₂ x))

theorem BoundedDerivs.compCLM {f : E → ℝ} (hf : BoundedDerivs f) (L : D →L[ℝ] E) :
    BoundedDerivs (fun x => f (L x)) := by
  obtain ⟨hf,C,A,hC,hA,hf₁,hf₂⟩ := hf
  let P : (E →L[ℝ] ℝ) →L[ℝ] D →L[ℝ] ℝ := (ContinuousLinearMap.compL ℝ D E ℝ).flip L
  have hP (B : E →L[ℝ] ℝ) : P B = B.comp L := rfl
  have hPn : ‖P‖ ≤ ‖L‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro B
    rw [hP]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq (mul_comm _ _)
  have hd := hf.differentiable (by norm_num)
  have hdd := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have heq : fderiv ℝ (fun x => f (L x)) = fun x => P (fderiv ℝ f (L x)) := by
    funext x
    exact ((hd (L x)).hasFDerivAt.comp x L.hasFDerivAt).fderiv
  refine ⟨hf.comp L.contDiff,C*‖L‖,A*‖L‖*‖L‖,
    mul_nonneg hC (norm_nonneg _),mul_nonneg (mul_nonneg hA (norm_nonneg _)) (norm_nonneg _),?_,?_⟩
  · intro x
    rw [heq]
    change ‖P (fderiv ℝ f (L x))‖ ≤ C*‖L‖
    rw [hP]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hf₁ _) (norm_nonneg _))
  · intro x
    have hsec : HasFDerivAt (fun x => P (fderiv ℝ f (L x)))
        (P.comp ((fderiv ℝ (fderiv ℝ f) (L x)).comp L)) x := by
      simpa only [Function.comp_def] using
        P.hasFDerivAt.comp x ((hdd (L x)).hasFDerivAt.comp x L.hasFDerivAt)
    rw [heq, hsec.fderiv]
    calc
      _ ≤ ‖P‖*‖(fderiv ℝ (fderiv ℝ f) (L x)).comp L‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖L‖*(A*‖L‖) := by
        gcongr
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_right (hf₂ _) (norm_nonneg _))
      _ = _ := by ring

end RegularAlgebra
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

def fiberGaussian : (n : ℕ) → ℝ → Measure (ParameterSpace n)
  | 0, x => Measure.dirac x
  | n+1, x => (fiberGaussian n x).prod (gaussianReal 0 1)

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
section GaussianGrowth
variable {E F : Type} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem HasExpGrowth.mul {f g : E → ℝ} (hf : HasExpGrowth f) (hg : HasExpGrowth g) :
    HasExpGrowth (fun x => f x*g x) := by
  obtain ⟨C,M,hC,hM,hf⟩ := hf
  obtain ⟨D,N,hD,hN,hg⟩ := hg
  refine ⟨C*D,M+N,mul_nonneg hC hD,add_nonneg hM hN,?_⟩
  intro x
  rw [norm_mul]
  calc
    _ ≤ (C*Real.exp (M*‖x‖))*(D*Real.exp (N*‖x‖)) :=
      mul_le_mul (hf x) (hg x) (norm_nonneg _) (by positivity)
    _ = _ := by rw [add_mul,Real.exp_add]; ring

theorem HasExpGrowth.integrable_gaussianMeasure [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : Measure E} [IsGaussian μ] {f : E → F}
    (hf : HasExpGrowth f) (hc : Continuous f) : Integrable f μ := by
  obtain ⟨C,M,hC,hM,hf⟩ := hf
  obtain ⟨a,ha,hi⟩ := IsGaussian.exists_integrable_exp_sq μ
  apply (hi.const_mul (C*Real.exp (M^2/a))).mono' hc.aestronglyMeasurable
  filter_upwards [] with x
  apply (hf x).trans
  rw [mul_assoc,← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.mpr
  have he : (M^2/a)*a = M^2 := div_mul_cancel₀ _ ha.ne'
  have hs := sq_nonneg (a*‖x‖-M/2)
  nlinarith [sq_nonneg M]

end GaussianGrowth

instance fiberGaussian_isGaussian : (n : ℕ) → (x : ℝ) → IsGaussian (fiberGaussian n x)
  | 0, x => inferInstanceAs (IsGaussian (Measure.dirac x))
  | n+1, x => by
      let := fiberGaussian_isGaussian n x
      exact inferInstanceAs (IsGaussian ((fiberGaussian n x).prod (gaussianReal 0 1)))

theorem HasExpGrowth.integrable_fiberGaussian {F : Type} [NormedAddCommGroup F]
    (n : ℕ) {f : ParameterSpace n → F} (hg : HasExpGrowth f) (hf : Continuous f) (x : ℝ) :
    Integrable f (fiberGaussian n x) := hg.integrable_gaussianMeasure hf

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
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_GrowthOperations
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
section GrowthOps
variable {E F : Type} [NormedAddCommGroup E] [NormedAddCommGroup F]

variable [NormedSpace ℝ F]
theorem HasExpGrowth.smul {f : E → ℝ} {g : E → F}
    (hf : HasExpGrowth f) (hg : HasExpGrowth g) : HasExpGrowth (fun z => f z • g z) := by
  obtain ⟨C,M,hC,hM,hf⟩ := hf
  obtain ⟨D,N,hD,hN,hg⟩ := hg
  refine ⟨C*D,M+N,mul_nonneg hC hD,add_nonneg hM hN,fun z => ?_⟩
  rw [norm_smul]
  calc
    ‖f z‖*‖g z‖ ≤ (C*Real.exp (M*‖z‖))*(D*Real.exp (N*‖z‖)) :=
      mul_le_mul (hf z) (hg z) (norm_nonneg _) (mul_nonneg hC (Real.exp_pos _).le)
    _ = _ := by rw [add_mul,Real.exp_add]; ring
end GrowthOps

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

@[reducible] def CascadeSpace (E : Type) : ℕ → Type
  | 0 => E
  | n+1 => CascadeSpace E n × ℝ

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
section Translate
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BoundedDerivs.translate {f : E → ℝ} (hf : BoundedDerivs f) (a : E) :
    BoundedDerivs (fun z => f (a+z)) := by
  obtain ⟨hf,C,D,hC,hD,h₁,h₂⟩ := hf
  have hd := hf.differentiable (by norm_num)
  have hdd := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have he : fderiv ℝ (fun z => f (a+z)) = fun z => fderiv ℝ f (a+z) := by
    funext z
    simpa only [ContinuousLinearMap.comp_id,Function.comp_def] using
      ((hd (a+z)).hasFDerivAt.comp z ((hasFDerivAt_id z).const_add a)).fderiv
  refine ⟨hf.comp (contDiff_const.add contDiff_id),C,D,hC,hD,?_,?_⟩
  · intro z; rw [he]; exact h₁ _
  · intro z
    rw [he]
    have H := ((hdd (a+z)).hasFDerivAt.comp z ((hasFDerivAt_id z).const_add a)).fderiv
    simp only [ContinuousLinearMap.comp_id,Function.comp_def] at H
    rw [H]
    exact h₂ _

end Translate
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

theorem BoundedDerivs.hasExpGrowth {f : E → ℝ} (hf : BoundedDerivs f) : HasExpGrowth f := by
  obtain ⟨hd,C,D,hC,_hD,h₁,_h₂⟩ := hf
  exact growth_of_fderiv_bound f (hd.differentiable (by norm_num)) hC h₁

end Generic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_DisorderPairs
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
namespace SK

def mixDisorder {n : ℕ} (a b : ℝ) (p : Disorder n × Disorder n) : Disorder n :=
  a • p.1 + b • p.2

def mixDisorderCLM (n : ℕ) (a b : ℝ) : (Disorder n × Disorder n) →L[ℝ] Disorder n :=
  a • ContinuousLinearMap.fst ℝ (Disorder n) (Disorder n) +
  b • ContinuousLinearMap.snd ℝ (Disorder n) (Disorder n)

@[simp] theorem mixDisorderCLM_apply {n : ℕ} (a b : ℝ) (p : Disorder n × Disorder n) :
    mixDisorderCLM n a b p = mixDisorder a b p := rfl

def rotateDisorder {n : ℕ} (θ : ℝ) (p : Disorder n × Disorder n) :
    Disorder n × Disorder n :=
  (mixDisorder (Real.cos θ) (Real.sin θ) p,
    mixDisorder (- Real.sin θ) (Real.cos θ) p)

def rotateDisorderCLM (n : ℕ) (θ : ℝ) :
    (Disorder n × Disorder n) →L[ℝ] Disorder n × Disorder n :=
  (mixDisorderCLM n (Real.cos θ) (Real.sin θ)).prod
    (mixDisorderCLM n (- Real.sin θ) (Real.cos θ))

@[simp] theorem rotateDisorderCLM_apply {n : ℕ} (θ : ℝ) (p : Disorder n × Disorder n) :
    rotateDisorderCLM n θ p = rotateDisorder θ p := rfl

theorem continuous_hamiltonian {n : ℕ} (x : Config n) :
    Continuous (fun J : Disorder n => hamiltonian J x) := by
  unfold hamiltonian
  fun_prop

end SK
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_LogPartition
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
namespace SK

@[simp] theorem rotateDisorder_pi_div_two_fst {n : ℕ} (p : Disorder n × Disorder n) :
    (rotateDisorder (Real.pi / 2) p).1 = p.2 := by
  funext e
  simp [rotateDisorder, mixDisorder]

end SK
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_GaugeSymmetry
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
namespace SK

def gaugeConfig {n : ℕ} (v x : Config n) : Config n := fun i => v i == x i

@[simp] theorem spin_beq (b c : Bool) : spin (b == c) = spin b * spin c := by
  cases b <;> cases c <;> norm_num [spin]

@[simp] theorem gaugeConfig_involutive {n : ℕ} (v x : Config n) :
    gaugeConfig v (gaugeConfig v x) = x := by
  funext i
  cases hv : v i <;> cases hx : x i <;> simp [gaugeConfig, hv, hx]

@[simp] theorem gaugeConfig_self {n : ℕ} (v : Config n) :
    gaugeConfig v v = fun _ => true := by
  funext i
  simp [gaugeConfig]

@[simp] theorem gaugeConfig_true {n : ℕ} (v : Config n) :
    gaugeConfig v (fun _ => true) = v := by
  funext i
  cases hv : v i <;> simp [gaugeConfig, hv]

end SK

end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_SpinMonomials
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

def spinMonomial {N : ℕ} (x : Config N) (I : Finset (Fin N)) : ℝ :=
  ∏ i ∈ I, spin (x i)

@[simp] theorem spinMonomial_sq {N : ℕ} (x : Config N) (I : Finset (Fin N)) :
    (spinMonomial x I)^2 = 1 := by
  simp only [spinMonomial,← Finset.prod_pow,spin_sq,Finset.prod_const_one]

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

omit [NormedSpace ℝ E] in
theorem HasExpGrowth.gaussian_integral {f : E × ℝ → F} (hf : HasExpGrowth f) :
    HasExpGrowth (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) := by
  obtain ⟨C,M,hC,hM,hf⟩ := hf
  let B := ∫ y : ℝ, Real.exp (M*|y|) ∂gaussianReal 0 1
  have hB : 0 ≤ B := integral_nonneg (fun y => (Real.exp_pos _).le)
  refine ⟨C*B,M,mul_nonneg hC hB,hM,?_⟩
  intro x
  have hb : ∀ y, ‖f (x,y)‖ ≤ C*Real.exp (M*‖x‖)*Real.exp (M*|y|) := by
    intro y
    apply (hf (x,y)).trans
    rw [mul_assoc,← Real.exp_add,← mul_add]
    apply mul_le_mul_of_nonneg_left _ hC
    apply Real.exp_le_exp.2
    apply mul_le_mul_of_nonneg_left _ hM
    rw [Prod.norm_def,Real.norm_eq_abs]
    exact max_le_add_of_nonneg (norm_nonneg x) (abs_nonneg y)
  calc
    _ ≤ ∫ y, ‖f (x,y)‖ ∂gaussianReal 0 1 := norm_integral_le_integral_norm _
    _ ≤ ∫ y, C*Real.exp (M*‖x‖)*Real.exp (M*|y|) ∂gaussianReal 0 1 :=
      integral_mono_of_nonneg (ae_of_all _ (fun _ => norm_nonneg _))
        ((integrable_exp_mul_abs_gaussian M).const_mul _) (ae_of_all _ hb)
    _ = _ := by rw [integral_const_mul]; dsimp [B]; ring

end ExponentialAverage

attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

end SK.Analytic

end
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

 theorem BoundedDerivs.integrableExpSet_section {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (x : E) : integrableExpSet (fun y => f (x,y)) (gaussianReal 0 1) = Set.univ := by
  ext m
  simp only [mem_univ,iff_true]
  exact hf.exp_integrable m x

 theorem BoundedDerivs.mem_interior_integrableExpSet_section {f : E × ℝ → ℝ}
    (hf : BoundedDerivs f) (x : E) (m : ℝ) :
    m ∈ interior (integrableExpSet (fun y => f (x,y)) (gaussianReal 0 1)) := by
  rw [hf.integrableExpSet_section,interior_univ]
  trivial

end Mass

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

abbrev BranchIncrement := ℝ × ℝ

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

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

abbrev ProductIncrement := Sum (ℝ × E) (ℝ × F)

end Vector

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_MatrixCovarianceAlgebra
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

def replicaCrossOverlap (N d : ℕ) (X Y : Fin N → Fin d → ℝ) (a b : Fin d) : ℝ :=
  (∑ i, X i a*Y i b)/(N:ℝ)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_MatrixSKGuerra
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

variable {S : Type} [Fintype S] [Nonempty S]

def MatrixStates (N d : ℕ) (D : Fin d → Fin d → ℝ) :=
  {s : Fin N → Config d // replicaCrossOverlap N d (fun i a => spin (s i a)) (fun i a => spin (s i a))=D}

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_RankOneMatrix
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

def replicaSpinMap (d : ℕ) : (Fin d → ℝ) →L[ℝ] (Config d → ℝ) :=
  ContinuousLinearMap.pi (fun s => ∑ i, spin (s i) • ContinuousLinearMap.proj i)

@[simp] theorem replicaSpinMap_apply (d : ℕ) (x : Fin d → ℝ) (s : Config d) :
    replicaSpinMap d x s=∑ i, spin (s i)*x i := by
  simp [replicaSpinMap]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_MatrixChain
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

section Penalty
variable {E : Type} [AddCommMonoid E]

def chainPotentialPenalty (F : E → ℝ) : List (ℝ × E) → E → ℝ
  | [], _ => 0
  | p::l, Q => p.1*(F (Q+p.2)-F Q)+chainPotentialPenalty F l (Q+p.2)

end Penalty

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

def rawVariance (l : List (ℝ × ℝ)) : ℝ := (l.map (fun p => p.2^2)).sum

def rawPenalty (l : List (ℝ × ℝ)) (q : ℝ) : ℝ :=
  chainPotentialPenalty (fun x : ℝ => x^2) (l.map (fun p => (p.1,p.2^2))) q

def rawArea (l : List (ℝ × ℝ)) : ℝ := (l.map (fun p => p.1*p.2^2)).sum

def weightedCross (l : List (ℝ × (ℝ × ℝ))) : ℝ := (l.map (fun p => p.2.1*p.2.2)).sum

def weightedVariance (l : List (ℝ × (ℝ × ℝ))) : ℝ := (l.map (fun p => p.2.2^2)).sum

def weightedCrossPenalty (l : List (ℝ × (ℝ × ℝ))) (g : ℝ) : ℝ :=
  chainPotentialPenalty (fun x : ℝ => x^2) (l.map (fun p => (p.1,p.2.1*p.2.2))) g

def weightedUnderlying (l : List (ℝ × (ℝ × ℝ))) : List (ℝ × ℝ) := l.map (fun p => (p.1,p.2.1))

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_WeightedListBridge
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

def zeroWeightChain (l : List (ℝ × ℝ)) : List (ℝ × (ℝ × ℝ)) := l.map (fun p => (p.1,(p.2,0)))

@[simp] theorem weightedUnderlying_zeroWeight (l : List (ℝ × ℝ)) : weightedUnderlying (zeroWeightChain l)=l := by
  simp only [weightedUnderlying,zeroWeightChain,List.map_map,Function.comp_def,Prod.mk.eta]
  exact List.map_id _

@[simp] theorem weightedUnderlying_append (l r : List (ℝ × (ℝ × ℝ))) :
    weightedUnderlying (l++r)=weightedUnderlying l++weightedUnderlying r := by
  simp only [weightedUnderlying,List.map_append]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleRetainedStats
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

def weightedAbsCross (w : List (ℝ × (ℝ × ℝ))) : ℝ := (w.map (fun p => |p.2.2| * |p.2.1|)).sum

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleScheduleScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
namespace SK.Analytic

section Scale
variable {E : Type} [SMul ℝ E]
def scaleIncrementChain (β : ℝ) (l : List (ℝ × E)) : List (ℝ × E) := l.map (fun p => (p.1,β • p.2))
end Scale

@[simp] theorem scaleIncrementChain_append {E : Type} [SMul ℝ E] (β : ℝ) (l r : List (ℝ × E)) :
    scaleIncrementChain β (l++r)=scaleIncrementChain β l++scaleIncrementChain β r := by
  simp only [scaleIncrementChain,List.map_append]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_ConstantWeightStats
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

def constantWeightChain (κ : ℝ) (l : List (ℝ × ℝ)) : List (ℝ × (ℝ × ℝ)) := l.map (fun p => (p.1,(p.2,κ*p.2)))

@[simp] theorem constantWeightChain_underlying (κ : ℝ) (l : List (ℝ × ℝ)) :
    weightedUnderlying (constantWeightChain κ l)=l := by
  simp only [weightedUnderlying,constantWeightChain,List.map_map,Function.comp_def,Prod.mk.eta]
  exact List.map_id _

@[simp] theorem constantWeightChain_variance (κ : ℝ) (l : List (ℝ × ℝ)) :
    weightedVariance (constantWeightChain κ l)=κ^2*rawVariance l := by
  induction l with
  | nil => simp [weightedVariance,rawVariance,constantWeightChain]
  | cons p l ih =>
    change (κ*p.2)^2+weightedVariance (constantWeightChain κ l)=κ^2*(p.2^2+rawVariance l)
    rw [ih]; ring

@[simp] theorem constantWeightChain_cross (κ : ℝ) (l : List (ℝ × ℝ)) :
    weightedCross (constantWeightChain κ l)=κ*rawVariance l := by
  induction l with
  | nil => simp [weightedCross,rawVariance,constantWeightChain]
  | cons p l ih =>
    change p.2*(κ*p.2)+weightedCross (constantWeightChain κ l)=κ*(p.2^2+rawVariance l)
    rw [ih]; ring

@[simp] theorem constantWeightChain_absCross (κ : ℝ) (l : List (ℝ × ℝ)) :
    weightedAbsCross (constantWeightChain κ l)=|κ| *rawVariance l := by
  induction l with
  | nil => simp [weightedAbsCross,rawVariance,constantWeightChain]
  | cons p l ih =>
    change |κ*p.2| * |p.2|+weightedAbsCross (constantWeightChain κ l)=|κ| *(p.2^2+rawVariance l)
    rw [abs_mul,ih,mul_assoc,show |p.2| * |p.2|=p.2^2 by rw [← sq,sq_abs]]
    ring

@[simp] theorem zeroWeightChain_append (l r : List (ℝ × ℝ)) : zeroWeightChain (l++r)=zeroWeightChain l++zeroWeightChain r := by
  simp only [zeroWeightChain,List.map_append]

@[simp] theorem weightedAbsCross_append (l r : List (ℝ × (ℝ × ℝ))) :
    weightedAbsCross (l++r)=weightedAbsCross l+weightedAbsCross r := by
  simp only [weightedAbsCross,List.map_append,List.sum_append]

@[simp] theorem weightedAbsCross_zeroWeight (l : List (ℝ × ℝ)) : weightedAbsCross (zeroWeightChain l)=0 := by
  simp [weightedAbsCross,zeroWeightChain,List.map_map,Function.comp_def]

@[simp] theorem zeroWeightChain_scale (β : ℝ) (l : List (ℝ × ℝ)) : scaleIncrementChain β (zeroWeightChain l)=zeroWeightChain (scaleIncrementChain β l) := by
  simp only [scaleIncrementChain,zeroWeightChain,List.map_map,Function.comp_def,Prod.smul_mk,smul_zero]

@[simp] theorem constantWeightChain_scale (β κ : ℝ) (l : List (ℝ × ℝ)) :
    scaleIncrementChain β (constantWeightChain κ l)=constantWeightChain κ (scaleIncrementChain β l) := by
  simp only [scaleIncrementChain,constantWeightChain,List.map_map]
  apply List.map_congr_left
  intro p hp
  apply Prod.ext
  · rfl
  apply Prod.ext
  · rfl
  change β*(κ*p.2)=κ*(β*p.2)
  ring

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_WeightedListMean
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

def weightedMean (w : List (ℝ × (ℝ × ℝ))) : ℝ := (w.map (fun p => p.2.2*p.2.1*p.1)).sum

@[simp] theorem weightedMean_append (v w : List (ℝ × (ℝ × ℝ))) : weightedMean (v++w)=weightedMean v+weightedMean w := by
  simp only [weightedMean,List.map_append,List.sum_append]

@[simp] theorem weightedMean_zeroWeight (t : List (ℝ × ℝ)) : weightedMean (zeroWeightChain t)=0 := by
  simp [weightedMean,zeroWeightChain,List.map_map,Function.comp_def]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_ConstantWeightMean
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

@[simp] theorem weightedMean_constantWeight (κ : ℝ) (l : List (ℝ × ℝ)) :
    weightedMean (constantWeightChain κ l)=κ*rawArea l := by
  induction l with
  | nil => simp [weightedMean,rawArea,constantWeightChain]
  | cons p l ih =>
    change κ*p.2*p.2*p.1+weightedMean (constantWeightChain κ l)=κ*(p.1*p.2^2+rawArea l)
    rw [ih]; ring

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowSchedule
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

abbrev NarrowMiddleIncrement := ProductIncrement (E:=ℝ × ℝ) (F:=ℝ × ℝ)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowRetainedFactor
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

abbrev NarrowRetainedState := (ℝ × ℝ) × (ℝ × ℝ)

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

def chainDuration (l : List (ℝ × ℝ≥0)) : ℝ≥0 := (l.map Prod.snd).sum

@[simp] theorem chainDuration_nil : chainDuration []=0 := rfl
@[simp] theorem chainDuration_cons (m : ℝ) (t : ℝ≥0) (l : List (ℝ × ℝ≥0)) :
    chainDuration ((m,t)::l)=t+chainDuration l := rfl

def TimeChainModels (α : ℝ → ℝ) : ℝ → List (ℝ × ℝ≥0) → Prop
  | _,[] => True
  | s,(m,t)::l => (∀ z ∈ Ico s (s+t), α z=m) ∧ TimeChainModels α (s+t) l

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_TimeChainPressureAlgebra
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

def chainQuadraticPenalty : ℝ → List (ℝ × ℝ≥0) → ℝ
  | _,[] => 0
  | s,p::ps => p.1*((s+(p.2:ℝ))^2-s^2)+chainQuadraticPenalty (s+p.2) ps

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_TimeIncrementBridge
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

def rawTimeChain (l : List (ℝ × ℝ≥0)) : List (ℝ × ℝ) := l.map (fun p => (p.1,Real.sqrt (p.2:ℝ)))

@[simp] theorem rawTimeChain_append (l r : List (ℝ × ℝ≥0)) : rawTimeChain (l++r)=rawTimeChain l++rawTimeChain r := by
  simp only [rawTimeChain,List.map_append]

@[simp] theorem rawVariance_rawTimeChain (l : List (ℝ × ℝ≥0)) : rawVariance (rawTimeChain l)=(chainDuration l:ℝ) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    change (Real.sqrt (p.2:ℝ))^2+rawVariance (rawTimeChain l)=((p.2+chainDuration l:ℝ≥0):ℝ)
    rw [Real.sq_sqrt p.2.coe_nonneg,ih,NNReal.coe_add]

@[simp] theorem rawArea_rawTimeChain (l : List (ℝ × ℝ≥0)) : rawArea (rawTimeChain l)=(l.map (fun p => p.1*(p.2:ℝ))).sum := by
  simp [rawArea,rawTimeChain,List.map_map,Function.comp_def,Real.sq_sqrt]

@[simp] theorem rawPenalty_rawTimeChain (l : List (ℝ × ℝ≥0)) (s : ℝ) : rawPenalty (rawTimeChain l) s=chainQuadraticPenalty s l := by
  induction l generalizing s with
  | nil => rfl
  | cons p l ih =>
    change p.1*((s+(Real.sqrt (p.2:ℝ))^2)^2-s^2)+rawPenalty (rawTimeChain l) (s+(Real.sqrt (p.2:ℝ))^2)=_
    rw [Real.sq_sqrt p.2.coe_nonneg,ih]
    rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_PartitionChain
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

@[simp] theorem chainDuration_append (l r : List (ℝ × ℝ≥0)) :
    chainDuration (l++r)=chainDuration l+chainDuration r := by
  simp [chainDuration]

theorem TimeChainModels.append {α : ℝ → ℝ} {s : ℝ} {l r : List (ℝ × ℝ≥0)}
    (hl : TimeChainModels α s l) (hr : TimeChainModels α (s+chainDuration l) r) :
    TimeChainModels α s (l++r) := by
  induction l generalizing s with
  | nil => simpa only [chainDuration_nil,NNReal.coe_zero,add_zero,List.nil_append] using hr
  | cons p l ih =>
    rcases p with ⟨m,t⟩
    rcases hl with ⟨hc,hl⟩
    exact ⟨hc,ih hl (by simpa only [chainDuration_cons,NNReal.coe_add,add_assoc] using hr)⟩

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_PositiveTimeChain
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

def positiveTimeChain (l : List (ℝ × ℝ≥0)) : List (ℝ × ℝ≥0) := l.filter (fun p => p.2≠0)

@[simp] theorem chainDuration_positiveTimeChain (l : List (ℝ × ℝ≥0)) :
    chainDuration (positiveTimeChain l)=chainDuration l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rcases p with ⟨m,d⟩
    by_cases hd : d=0
    · simpa [positiveTimeChain,hd,chainDuration_cons] using ih
    · simp only [SK.Analytic.positiveTimeChain,List.filter_cons,hd,ne_eq,not_false_eq_true,decide_true,ite_true,chainDuration_cons] at *
      rw [ih]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_TimeChainOn
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

structure TimeChainOn (α : ℝ → ℝ) (s t : ℝ) where
  chain : List (ℝ × ℝ≥0)
  duration : (chainDuration chain:ℝ)=t-s
  mass : ∀ p∈chain,p.1∈Icc (0:ℝ) 1
  positive : ∀ p∈chain,0<p.2
  models : TimeChainModels α s chain

def TimeChainOn.append {α : ℝ → ℝ} {s t u : ℝ} (l : TimeChainOn α s t) (r : TimeChainOn α t u) : TimeChainOn α s u where
  chain := l.chain++r.chain
  duration := by rw [chainDuration_append,NNReal.coe_add,l.duration,r.duration]; ring
  mass := by intro p hp; rcases List.mem_append.mp hp with hp|hp; exact l.mass p hp; exact r.mass p hp
  positive := by intro p hp; rcases List.mem_append.mp hp with hp|hp; exact l.positive p hp; exact r.positive p hp
  models := l.models.append (by simpa only [l.duration,add_sub_cancel] using r.models)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_WeightedAugment
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

@[simp] theorem weightedVariance_append (l r : List (ℝ × (ℝ × ℝ))) :
    weightedVariance (l++r)=weightedVariance l+weightedVariance r := by
  simp [weightedVariance,List.sum_append]

@[simp] theorem weightedCross_append (l r : List (ℝ × (ℝ × ℝ))) :
    weightedCross (l++r)=weightedCross l+weightedCross r := by
  simp [weightedCross,List.sum_append]

@[simp] theorem weightedVariance_zeroWeight (l : List (ℝ × ℝ)) : weightedVariance (zeroWeightChain l)=0 := by
  simp [weightedVariance,zeroWeightChain,List.map_map,Function.comp_def]

@[simp] theorem weightedCross_zeroWeight (l : List (ℝ × ℝ)) : weightedCross (zeroWeightChain l)=0 := by
  simp [weightedCross,zeroWeightChain,List.map_map,Function.comp_def]

@[simp] theorem weightedCrossPenalty_zeroWeight (l : List (ℝ × ℝ)) (g : ℝ) :
    weightedCrossPenalty (zeroWeightChain l) g=0 := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    change p.1*((g+p.2*0)^2-g^2)+weightedCrossPenalty (zeroWeightChain l) (g+p.2*0)=0
    simp only [mul_zero,add_zero,sub_self,ih]

@[simp] theorem weightedVariance_full (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) :
    weightedVariance (zeroWeightChain c++w++zeroWeightChain t)=weightedVariance w := by simp

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowTimeBlocks
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

structure NarrowTimeBlocks (α : ℝ → ℝ) (r h q : ℝ) where
  before : TimeChainOn α 0 (r-h)
  left : TimeChainOn α (r-h) r
  right : TimeChainOn α r (r+h)
  after : TimeChainOn α (r+h) q
  tail : TimeChainOn α q 1

namespace NarrowTimeBlocks
variable {α : ℝ → ℝ} {r h q : ℝ} (B : NarrowTimeBlocks α r h q)

def common : TimeChainOn α 0 r := B.before.append B.left
def middle : TimeChainOn α r q := B.right.append B.after
def front : TimeChainOn α 0 q := B.common.append B.middle
def full : TimeChainOn α 0 1 := B.front.append B.tail

def b : List (ℝ × ℝ) := rawTimeChain B.before.chain
def l : List (ℝ × ℝ) := rawTimeChain B.left.chain
def j : List (ℝ × ℝ) := rawTimeChain B.right.chain
def k : List (ℝ × ℝ) := rawTimeChain B.after.chain
def t : List (ℝ × ℝ) := rawTimeChain B.tail.chain

def c (a : ℝ) : List (ℝ × (ℝ × ℝ)) := zeroWeightChain B.b++constantWeightChain (a/h) B.l
def v (θ : ℝ) : List (ℝ × (ℝ × ℝ)) := constantWeightChain (θ/h) B.j++zeroWeightChain B.k
def w (a : ℝ) : List (ℝ × (ℝ × ℝ)) := constantWeightChain (-a/h) B.j++zeroWeightChain B.k

@[simp] theorem c_underlying (a : ℝ) : weightedUnderlying (B.c a)=B.b++B.l := by
  simp only [c,weightedUnderlying_append,weightedUnderlying_zeroWeight,constantWeightChain_underlying]
@[simp] theorem v_underlying (θ : ℝ) : weightedUnderlying (B.v θ)=B.j++B.k := by
  simp only [v,weightedUnderlying_append,weightedUnderlying_zeroWeight,constantWeightChain_underlying]
@[simp] theorem w_underlying (a : ℝ) : weightedUnderlying (B.w a)=B.j++B.k := by
  simp only [w,weightedUnderlying_append,weightedUnderlying_zeroWeight,constantWeightChain_underlying]

@[simp] theorem l_variance : rawVariance B.l=h := by
  rw [l,rawVariance_rawTimeChain,B.left.duration]; ring
@[simp] theorem j_variance : rawVariance B.j=h := by
  rw [j,rawVariance_rawTimeChain,B.right.duration]; ring

end NarrowTimeBlocks

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

def oneConfigEquiv : Bool ≃ Config 1 where
  toFun b := fun _ => b
  invFun s := s 0
  left_inv _ := rfl
  right_inv s := funext (fun i => congrArg s (Subsingleton.elim 0 i))

@[simp] theorem oneConfigEquiv_apply (b : Bool) (i : Fin 1) : oneConfigEquiv b i=b := rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarHierarchyAverageAlgebra
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

structure BoundedScalar (g : ℝ → ℝ) : Prop where
  continuous : Continuous g
  bounded : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |g x| ≤ B

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_WeightedSplitPath
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

abbrev MarkedWeightedState := (ℝ × ℝ) × ℝ

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

class Model (n : ℕ) where
  logPartition : ℝ → Disorder n → ℝ
  gibbs : ℝ → Disorder n → Config n → ℝ
  gibbs_nonneg : ∀ β J x, 0 ≤ gibbs β J x
  gibbs_sum : ∀ β J, ∑ x, gibbs β J x = 1
  continuous_gibbs : ∀ β x, Continuous (fun J => gibbs β J x)
  continuous_logPartition : ∀ β, Continuous (logPartition β)
  hasDerivAt : ∀ (β : ℝ) (J : ℝ → Disorder n) (K : Disorder n) (s : ℝ),
    (∀ x, HasDerivAt (fun t => hamiltonian (J t) x) (hamiltonian K x) s) →
    HasDerivAt (fun t => logPartition β (J t))
      (β * ∑ x, gibbs β (J s) x * hamiltonian K x) s

@[simp] theorem rotateDisorder_pi_div_two_fst {n : ℕ} [Model n] (p : Disorder n × Disorder n) :
    (rotateDisorder (Real.pi / 2) p).1 = p.2 := by
  funext e
  simp [rotateDisorder, mixDisorder]

end SK.Analytic.SmoothFamily

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_RestrictedReplicas
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

abbrev ReplicaConfig (n d : ℕ) := Fin d → Config n

def replicaEnergy {n d : ℕ} (J : Disorder n) (s : ReplicaConfig n d) : ℝ :=
  ∑ a, hamiltonian J (s a)

def restrictedPartition {n d : ℕ} (β : ℝ) (S : Finset (ReplicaConfig n d)) (J : Disorder n) : ℝ :=
  ∑ s ∈ S, Real.exp (β*replicaEnergy J s)

def restrictedLogPartition {n d : ℕ} (β : ℝ) (S : Finset (ReplicaConfig n d)) (J : Disorder n) : ℝ :=
  Real.log (restrictedPartition β S J)

def replicaRow {n d : ℕ} (β : ℝ) (S : Finset (ReplicaConfig n d)) (J : Disorder n)
    (s : ReplicaConfig n d) : ℝ := Real.exp (β*replicaEnergy J s)/restrictedPartition β S J

def replicaMarginal {n d : ℕ} (β : ℝ) (S : Finset (ReplicaConfig n d)) (J : Disorder n)
    (x : Config n) : ℝ := ∑ s ∈ S, ∑ a : Fin d, if s a = x then replicaRow β S J s/(d:ℝ) else 0

theorem restrictedPartition_pos {n d : ℕ} (β : ℝ) {S : Finset (ReplicaConfig n d)}
    (hS : S.Nonempty) (J : Disorder n) : 0 < restrictedPartition β S J :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) hS

theorem replicaRow_nonneg {n d : ℕ} (β : ℝ) {S : Finset (ReplicaConfig n d)}
    (hS : S.Nonempty) (J : Disorder n) (s : ReplicaConfig n d) : 0 ≤ replicaRow β S J s :=
  div_nonneg (Real.exp_nonneg _) (restrictedPartition_pos β hS J).le

theorem replicaRow_sum {n d : ℕ} (β : ℝ) {S : Finset (ReplicaConfig n d)}
    (hS : S.Nonempty) (J : Disorder n) : ∑ s ∈ S, replicaRow β S J s = 1 := by
  simp only [replicaRow,← Finset.sum_div]
  exact div_self (restrictedPartition_pos β hS J).ne'

theorem replicaMarginal_nonneg {n d : ℕ} (β : ℝ) {S : Finset (ReplicaConfig n d)}
    (hS : S.Nonempty) (J : Disorder n) (x : Config n) : 0 ≤ replicaMarginal β S J x := by
  apply Finset.sum_nonneg
  intro s _
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact div_nonneg (replicaRow_nonneg β hS J s) (by positivity)
  · rfl

theorem replicaMarginal_sum {n d : ℕ} (hd : 0 < d) (β : ℝ) {S : Finset (ReplicaConfig n d)}
    (hS : S.Nonempty) (J : Disorder n) : ∑ x, replicaMarginal β S J x = 1 := by
  have H (s : ReplicaConfig n d) :
      (∑ x : Config n, ∑ a : Fin d, if s a = x then replicaRow β S J s/(d:ℝ) else 0) =
        replicaRow β S J s := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul]
    have hd' : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp
  unfold replicaMarginal
  rw [Finset.sum_comm]
  simp_rw [H]
  exact replicaRow_sum β hS J

theorem replicaMarginal_energy {n d : ℕ} (β : ℝ) (S : Finset (ReplicaConfig n d))
    (J K : Disorder n) :
    ∑ x, replicaMarginal β S J x*hamiltonian K x =
      (∑ s ∈ S, replicaRow β S J s*replicaEnergy K s)/(d:ℝ) := by
  have H (s : ReplicaConfig n d) :
      (∑ x : Config n, ∑ a : Fin d, (if s a = x then replicaRow β S J s/(d:ℝ) else 0)*
        hamiltonian K x) = replicaRow β S J s*replicaEnergy K s/(d:ℝ) := by
    rw [Finset.sum_comm]
    simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    unfold replicaEnergy
    rw [Finset.mul_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    ring
  unfold replicaMarginal
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [H]
  rw [Finset.sum_div]

theorem continuous_replicaEnergy {n d : ℕ} (s : ReplicaConfig n d) :
    Continuous (fun J : Disorder n => replicaEnergy J s) :=
  continuous_finsetSum _ (fun a _ => continuous_hamiltonian (s a))

theorem continuous_restrictedPartition {n d : ℕ} (β : ℝ) (S : Finset (ReplicaConfig n d)) :
    Continuous (restrictedPartition β S) :=
  continuous_finsetSum _ (fun s _ => (Real.continuous_exp.comp ((continuous_replicaEnergy s).const_mul β)))

theorem continuous_restrictedLogPartition {n d : ℕ} (β : ℝ) {S : Finset (ReplicaConfig n d)}
    (hS : S.Nonempty) : Continuous (restrictedLogPartition β S) :=
  (continuous_restrictedPartition β S).log (fun J => (restrictedPartition_pos β hS J).ne')

theorem continuous_replicaRow {n d : ℕ} (β : ℝ) {S : Finset (ReplicaConfig n d)}
    (hS : S.Nonempty) (s : ReplicaConfig n d) : Continuous (fun J => replicaRow β S J s) :=
  (Real.continuous_exp.comp ((continuous_replicaEnergy s).const_mul β)).div (continuous_restrictedPartition β S)
    (fun J => (restrictedPartition_pos β hS J).ne')

theorem continuous_replicaMarginal {n d : ℕ} (β : ℝ) {S : Finset (ReplicaConfig n d)}
    (hS : S.Nonempty) (x : Config n) : Continuous (fun J => replicaMarginal β S J x) := by
  apply continuous_finsetSum
  intro s _
  apply continuous_finsetSum
  intro a _
  by_cases h : s a = x
  · simp only [ite_eq_left h]
    exact (continuous_replicaRow β hS s).div_const _
  · simp only [ite_eq_right h]
    exact continuous_const

theorem restrictedLogPartition_hasDerivAt {n d : ℕ} (β : ℝ) {S : Finset (ReplicaConfig n d)}
    (hS : S.Nonempty) (J : ℝ → Disorder n) (K : Disorder n) (t : ℝ)
    (hJ : ∀ x, HasDerivAt (fun u => hamiltonian (J u) x) (hamiltonian K x) t) :
    HasDerivAt (fun u => restrictedLogPartition β S (J u))
      (β*∑ s ∈ S, replicaRow β S (J t) s*replicaEnergy K s) t := by
  have he (s : ReplicaConfig n d) :
      HasDerivAt (fun u => replicaEnergy (J u) s) (replicaEnergy K s) t :=
    HasDerivAt.fun_sum (fun a _ => hJ (s a))
  have hp : HasDerivAt (fun u => restrictedPartition β S (J u))
      (∑ s ∈ S, Real.exp (β*replicaEnergy (J t) s)*(β*replicaEnergy K s)) t :=
    HasDerivAt.fun_sum (fun s _ => ((he s).const_mul β).exp)
  have hl := hp.log (restrictedPartition_pos β hS (J t)).ne'
  apply hl.congr_deriv
  simp only [replicaRow,Finset.sum_div,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

@[instance_reducible] def restrictedModel {n d : ℕ} (hd : 0 < d) (S : Finset (ReplicaConfig n d))
    (hS : S.Nonempty) : SmoothFamily.Model n where
  logPartition γ := restrictedLogPartition (γ/(d:ℝ)) S
  gibbs γ := replicaMarginal (γ/(d:ℝ)) S
  gibbs_nonneg γ := replicaMarginal_nonneg _ hS
  gibbs_sum γ := replicaMarginal_sum hd _ hS
  continuous_gibbs γ := continuous_replicaMarginal _ hS
  continuous_logPartition γ := continuous_restrictedLogPartition _ hS
  hasDerivAt γ J K t hJ := by
    have H := restrictedLogPartition_hasDerivAt (γ/(d:ℝ)) hS J K t hJ
    apply H.congr_deriv
    rw [replicaMarginal_energy]
    ring

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_PairTerminal
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

def pairSpinMap : (ℝ × ℝ) →L[ℝ] (Config 2 → ℝ) :=
  ContinuousLinearMap.pi (fun s => spin (s 0) • ContinuousLinearMap.fst ℝ ℝ ℝ+
    spin (s 1) • ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] theorem pairSpinMap_apply (p : ℝ × ℝ) (s : Config 2) :
    pairSpinMap p s=spin (s 0)*p.1+spin (s 1)*p.2 := rfl

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

def replicaFlip {n d : ℕ} (a : Fin d) (s : ReplicaConfig n d) : ReplicaConfig n d :=
  fun i => if i=a then flip (s i) else s i

@[simp] theorem replicaFlip_apply_same {n d : ℕ} (a : Fin d) (s : ReplicaConfig n d) :
    replicaFlip a s a=flip (s a) := by simp [replicaFlip]

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

structure GreedyRecord (n : ℕ) where
  refs : ℕ → Config n
  time : ℕ
  kept : Finset ℕ

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_GridThreshold
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

namespace FiniteLaw

def uniformFin (n : ℕ) (hn : 0 < n) : FiniteLaw (Fin n) where
  weight _ := 1/(n:ℝ)
  nonneg _ := by positivity
  sum_one := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp

end FiniteLaw

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_ProtectedBlock
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

def IsRetainedSuffix (A D : Finset ℕ) : Prop :=
  D ⊆ A ∧ ∀ ⦃i j : ℕ⦄, i ∈ D → j ∈ A → i ≤ j → j ∈ D

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_ProtectedStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SK.Analytic

def BlockProtected (B j : ℕ) (A : Finset ℕ) : Prop :=
  (∀ i,(j-1)/B*B ≤ i → i < j → i ∈ A) ∧ (∀ k, k*B < j → k*B ∈ A)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_ThresholdObstruction
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

structure GreedyScaleBounds (n B H p : ℕ) (t ρ d b b' q : ℝ) : Prop where
  p_pos : 0<p
  B_pos : 0<B
  HB : H<B
  packingH : ⌈2/b^2⌉₊≤H
  t_pos : 0<t
  rho_pos : 0<ρ
  d_nonneg : 0≤d
  b_pos : 0<b
  packing : 3*t<b^2/2
  cutoff : 3*t<b
  total_error : 6*p*ρ^20<t
  small_cutoff : 2*t+6*p*ρ^20+2*(n:ℝ)^(-(1:ℝ)/100)<b'
  separation : 12*p*ρ^20+4*(n:ℝ)^(-(1:ℝ)/100)<3*ρ
  width : ρ^8<t/2
  small_width : 6*p*ρ^20+2*(n:ℝ)^(-(1:ℝ)/100)+ρ^20+d/2<ρ^8
  large_width : 6*p*ρ^20+2*(n:ℝ)^(-(1:ℝ)/100)+ρ^20+3*d/2≤2*ρ
  jump : d/2≤ρ^20
  eta : 2*(n:ℝ)^(-(1:ℝ)/100)<2*ρ^20
  high : 2*t+6*p*ρ^20+2*(n:ℝ)^(-(1:ℝ)/100)+2*ρ^20<q
  grid_range : 4*p*ρ≤t

end SK.Analytic

end
end

end OAI
end



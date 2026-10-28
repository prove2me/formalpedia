-- Prove2me | Definitions.Def_OAIQ036S003
-- name    : OAIQ036S003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T04:49:06.826508+00:00
-- url     : https://prove2.me/theorems/02260e06-9457-4918-b4b6-732f695041f7
-- title:
--   Definitions bundle OAIQ036S003 of the split of OpenAI, Stretched-exponential barriers for typical SK initial states
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SK.main`, carved from OpenAI's openai/math development (OpenAI, *Stretched-exponential barriers for typical SK initial states*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 99 declarations of OpenAI's Lean: 61 definitions, 6 instances and 32 theorems. The definitions and types are `OAI.SK.Analytic.fiberMeasure`, `OAI.SK.Analytic.fourBlockCommon`, `OAI.SK.Analytic.fourBlockFuture`, `OAI.SK.Analytic.fourBlockLeft`, `OAI.SK.Analytic.fourBlockMiddle`, `OAI.SK.Analytic.fourBlockRight`, `OAI.SK.Analytic.fourBlockTent`, `OAI.SK.Analytic.gibbsEnergyTail`, `OAI.SK.Analytic.greedyReference`, `OAI.SK.Analytic.greedyRun`, `OAI.SK.Analytic.hierarchyLevel`, `OAI.SK.Analytic.mapProductIncrement`, `OAI.SK.Analytic.markedScalarVector`, `OAI.SK.Analytic.markedWeightedChain`, `OAI.SK.Analytic.matrixChainPenalty`, `OAI.SK.Analytic.matrixConstrainedPressure`, `OAI.SK.Analytic.matrixSKLogPartition`, `OAI.SK.Analytic.matrixSKObservables`, `OAI.SK.Analytic.mergedProductBranches`, `OAI.SK.Analytic.narrowAbsCross`, `OAI.SK.Analytic.narrowCommonEmbedding`, `OAI.SK.Analytic.narrowCrossPenalty`, `OAI.SK.Analytic.narrowMiddleNoise`, `OAI.SK.Analytic.narrowMiddleSchedule`, `OAI.SK.Analytic.narrowMiddleVector`, `OAI.SK.Analytic.narrowNoisePenalty`, `OAI.SK.Analytic.narrowQuarticPenalty`, `OAI.SK.Analytic.narrowRetainedCommon`, `OAI.SK.Analytic.narrowRetainedEmbedding`, `OAI.SK.Analytic.narrowRetainedMiddle`, `OAI.SK.Analytic.narrowRetainedPrefix`, `OAI.SK.Analytic.narrowSchedule`, `OAI.SK.Analytic.narrowToTriple`, `OAI.SK.Analytic.narrowVariance`, `OAI.SK.Analytic.overlapCode`, `OAI.SK.Analytic.pairSpinObservable`, `OAI.SK.Analytic.productLeft`, `OAI.SK.Analytic.productMass`, `OAI.SK.Analytic.productRight`, `OAI.SK.Analytic.productVector` and 21 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability/SKBarriers, in whole or in part: `SKBarriers_Calculus_CubeMeasures`, `SKBarriers_Calculus_CubeMoments`, `SKBarriers_Calculus_ParameterBilinear`, `SKBarriers_Calculus_ParameterFiniteLog`, `SKBarriers_Calculus_ParameterProducts`, `SKBarriers_Coverage_EnergyTail`, `SKBarriers_Coverage_PressureGapFiniteInf`, `SKBarriers_Coverage_ThermodynamicLimit`, `SKBarriers_Dynamics_GreedyRecursion`, `SKBarriers_Dynamics_HeatBathChoice`, `SKBarriers_Gaussian_FiberGaussian`, `SKBarriers_Gaussian_GaussianStepCalculus`, `SKBarriers_Hierarchy_ConstantWeightMean`, `SKBarriers_Hierarchy_HierarchyLevels`, `SKBarriers_Hierarchy_WeightedMarkedIntegral`, `SKBarriers_Hierarchy_WeightedMoments`, `SKBarriers_Hierarchy_WeightedSplitPath`, `SKBarriers_Interpolation_RestrictedConcentration`, `SKBarriers_Interpolation_SKBlockCoordinates`, `SKBarriers_Locking_FourBlockQuadratic`, `SKBarriers_Locking_FourBlockTent`, `SKBarriers_Locking_NarrowRetainedCommon`, `SKBarriers_Locking_NarrowRetainedExpansion`, `SKBarriers_Locking_NarrowRetainedFactor`, `SKBarriers_Locking_NarrowRetainedStats`, `SKBarriers_Locking_NarrowSchedule`, `SKBarriers_Locking_NarrowScheduleEndpoint`, `SKBarriers_Locking_OverlapPacking`, `SKBarriers_Parisi_CDFAtomicRepresentation`, `SKBarriers_Parisi_CDFUniformQuantiles`, `SKBarriers_Parisi_QuantileChain`, `SKBarriers_Replicas_MatrixChain`, `SKBarriers_Replicas_MatrixSKCovariance`, `SKBarriers_Replicas_MatrixSKGuerra`, `SKBarriers_Replicas_OverlapCode`, `SKBarriers_Replicas_PairTerminal`, `SKBarriers_Replicas_ProductMerge`, `SKBarriers_Replicas_TripleDecoupling`, `SKBarriers_Replicas_TripleScaleStats`, `SKBarriers_Replicas_TripleSchedule`, `SKBarriers_Replicas_VectorBranch`, `SKBarriers_Scalar_PartitionChain`, `SKBarriers_Scalar_ProductBranchMap`, `SKBarriers_Scalar_ScalarListBounds`, `SKBarriers_Scalar_VectorBlocks`, `SKBarriers_Scalar_VectorHierarchy`, `SKBarriers_SpinGlass_Basic`, `SKBarriers_SpinGlass_DisorderPairs`, `SKBarriers_SpinGlass_GaugeSymmetry`, `SKBarriers_SpinGlass_LogPartition`, `SKBarriers_SpinGlass_SpinMonomials`.
--
--   **Imports.** It imports the published bundle `Def_SKBarriers`; the bundles `OAIQ036S000` and `OAIQ036S001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ036S004` and `OAIQ036S005`; the statements `OAI.SK.Analytic.coverage_energy_tail`, `OAI.SK.Analytic.identity_main_of_static_locking` and `OAI.SK.Analytic.signed_small_scale`.
-- source:
--   OpenAI, Stretched-exponential barriers for typical SK initial states, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Stretched-exponential-barriers-for-typical-SK-initial-states-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability/SKBarriers at commit adc7f12

import Mathlib
import Definitions.Def_SKBarriers
import Definitions.Def_OAIQ036S000
import Definitions.Def_OAIQ036S001

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

def fiberMeasure : (n : ℕ) → ℝ → Measure (ParameterSpace n)
  | 0, x => Measure.dirac x
  | n+1, x => (fiberMeasure n x).prod volume

instance fiberSigmaFinite : (n : ℕ) → (x : ℝ) → SigmaFinite (fiberMeasure n x)
  | 0, x => inferInstanceAs (SigmaFinite (Measure.dirac x))
  | n+1, x => letI := fiberSigmaFinite n x; inferInstanceAs (SigmaFinite ((fiberMeasure n x).prod volume))

end SK.Analytic

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_ParameterProducts
attribute [-instance] _root_.OAI.SK.Analytic.fiberGaussian_isGaussian _root_.OAI.SK.Analytic.fiberSigmaFinite _root_.OAI.SK.Analytic.parameterBorel _root_.OAI.SK.Analytic.parameterMeasurable _root_.OAI.SK.Analytic.parameterSecondCountable
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

def tiltedPotential (n : ℕ) (V : ParameterSpace n → ℝ) (L : ParameterSpace n →L[ℝ] ℝ)
    (K : ℝ) (z : ParameterSpace n) : ℝ :=
  V z - parameter n z * L z + (K/2)*(parameter n z*parameter n z)

end SK.Analytic

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_CubeMoments
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
instance fiberNeZero : (n : ℕ) → (x : ℝ) → NeZero (fiberMeasure n x)
  | 0, x => inferInstanceAs (NeZero (Measure.dirac x))
  | n+1, x => by
    let := fiberNeZero n x
    refine ⟨Measure.measure_univ_ne_zero.mp ?_⟩
    change ((fiberMeasure n x).prod volume) univ ≠ 0
    rw [← univ_prod_univ, Measure.prod_prod]
    exact mul_ne_zero (NeZero.ne _) (NeZero.ne _)

end SK.Analytic

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

theorem partition_pos {n : ℕ} (β : ℝ) (J : Disorder n) : 0 < partition β J := by
  unfold partition
  exact Finset.sum_pos (fun x _ => Real.exp_pos _) Finset.univ_nonempty

theorem gibbs_pos {n : ℕ} (β : ℝ) (J : Disorder n) (x : Config n) :
    0 < gibbs β J x := by
  exact div_pos (Real.exp_pos _) (partition_pos β J)

theorem gibbs_sum {n : ℕ} (β : ℝ) (J : Disorder n) :
    ∑ x : Config n, gibbs β J x = 1 := by
  simp only [gibbs, ← Finset.sum_div]
  exact div_self (ne_of_gt (partition_pos β J))

instance disorderLaw_probability (n : ℕ) : IsProbabilityMeasure (disorderLaw n) := by
  unfold disorderLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

end SK
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

theorem gaussianTransition_density {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (m : ℝ) (x : E) (y : ℝ) :
    Real.exp (m*(f (x,y)-gaussianStep m f x)) =
      Real.exp (m*f (x,y)) / (∫ z, Real.exp (m*f (x,z)) ∂gaussianReal 0 1) := by
  by_cases hm : m = 0
  · subst m
    simp
  · have hpos := integral_exp_pos (hf.exp_integrable m x)
    rw [gaussianStep,ite_eq_right hm,positiveGaussianLogStep]
    have he : m*(f (x,y)-Real.log (∫ z, Real.exp (m*f (x,z)) ∂gaussianReal 0 1)/m) =
        m*f (x,y)-Real.log (∫ z, Real.exp (m*f (x,z)) ∂gaussianReal 0 1) := by
      rw [mul_sub, mul_div_cancel₀ _ hm]
    rw [he,Real.exp_sub,Real.exp_log hpos]

theorem gaussianTransition_integral_one {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (m : ℝ) (x : E) :
    (∫ y, Real.exp (m*(f (x,y)-gaussianStep m f x)) ∂gaussianReal 0 1) = 1 := by
  simp_rw [gaussianTransition_density hf]
  rw [integral_div,div_self (integral_exp_pos (hf.exp_integrable m x)).ne']

theorem gaussianStepLaw_integral {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × ℝ → ℝ} (hf : BoundedDerivs f) (m : ℝ) (x : E) (g : ℝ → F) :
    (∫ y, g y ∂gaussianStepLaw m f x) =
      ∫ y, Real.exp (m*(f (x,y)-gaussianStep m f x)) • g y ∂gaussianReal 0 1 := by
  rw [gaussianStepLaw,integral_tilted]
  simp_rw [gaussianTransition_density hf]

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

theorem paramRegular_bilinear (B : P →L[ℝ] E →L[ℝ] ℝ) :
    ParamRegular (fun z : P × E => B z.1 z.2) := by
  have hc : ContDiff ℝ 2 (fun z : P × E => B z.1 z.2) := B.isBoundedBilinearMap.contDiff
  have he : fderiv ℝ (fun z : P × E => B z.1 z.2) = fun z => B.deriv₂ z := by
    funext z
    rw [B.isBoundedBilinearMap.fderiv]
    apply ContinuousLinearMap.ext
    intro v
    rfl
  refine ⟨hc,?_,?_,?_⟩
  · intro R
    refine ⟨‖B‖*max R 0,by positivity,?_⟩
    intro p e hp
    calc
      |B p e| = ‖B p e‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖B p‖*‖e‖ := (B p).le_opNorm e
      _ ≤ (‖B‖*‖p‖)*‖e‖ := mul_le_mul_of_nonneg_right (B.le_opNorm p) (norm_nonneg e)
      _ ≤ (‖B‖*max R 0)*(1+‖e‖) := by
        gcongr
        · exact hp.trans (le_max_left _ _)
        · linarith
  · rw [he]
    exact ParamExpGrowth.continuousLinearMap B.deriv₂
  · rw [he]
    intro R
    refine ⟨‖B.deriv₂‖,0,ContinuousLinearMap.opNorm_nonneg _,le_rfl,?_⟩
    intro p e _
    rw [B.deriv₂.fderiv]
    simp only [zero_mul,Real.exp_zero,mul_one]
    exact le_rfl
end ParameterBilinear
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

omit [NormedSpace ℝ P] [NormedSpace ℝ E] in
theorem param_inv_finite_exp_growth (f : S → P × E → ℝ)
    (hf : ∀ s, ParamLinearGrowth (f s)) :
    ParamExpGrowth (fun z => (∑ s, Real.exp (f s z))⁻¹) := by
  classical
  let s₀ : S := Classical.arbitrary S
  apply ((hf s₀).exp_mul (-1)).of_norm_le zero_le_one
  intro z
  have hp : 0 < ∑ s, Real.exp (f s z) := Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have hs : Real.exp (f s₀ z) ≤ ∑ s, Real.exp (f s z) :=
    Finset.single_le_sum (fun s _ => (Real.exp_pos (f s z)).le) (Finset.mem_univ s₀)
  rw [one_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (inv_pos.2 hp),abs_of_pos (Real.exp_pos _),
    neg_one_mul,Real.exp_neg]
  exact (inv_le_inv₀ hp (Real.exp_pos _)).2 hs

omit [NormedSpace ℝ P] [NormedSpace ℝ E] in
theorem param_log_finite_exp_linear (f : S → P × E → ℝ)
    (hf : ∀ s, ParamLinearGrowth (f s)) :
    ParamLinearGrowth (fun z => Real.log (∑ s, Real.exp (f s z))) := by
  classical
  intro R
  choose C hC hb using fun s => hf s R
  let D := ∑ s, C s
  let N : ℝ := Fintype.card S
  have hD : 0 ≤ D := Finset.sum_nonneg (fun s _ => hC s)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos (α := S)
  refine ⟨D+|Real.log N|,by positivity,?_⟩
  intro p e hp
  let A := D*(1+‖e‖)
  let Z := ∑ s, Real.exp (f s (p,e))
  have hz : 0 < Z := Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have hh s : |f s (p,e)| ≤ A := by
    apply (hb s p e hp).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact Finset.single_le_sum (fun t _ => hC t) (Finset.mem_univ s)
  have hu' : Z ≤ N*Real.exp A := by
    calc
      Z ≤ ∑ _ : S, Real.exp A := Finset.sum_le_sum (fun s _ =>
        Real.exp_le_exp.2 ((le_abs_self _).trans (hh s)))
      _ = N*Real.exp A := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,N]
  let s₀ : S := Classical.arbitrary S
  have hl' : Real.exp (-A) ≤ Z := by
    calc
      _ ≤ Real.exp (f s₀ (p,e)) := Real.exp_le_exp.2 (abs_le.1 (hh s₀)).1
      _ ≤ Z := Finset.single_le_sum (fun s _ => (Real.exp_pos (f s (p,e))).le) (Finset.mem_univ s₀)
  have hu := Real.log_le_log hz hu'
  have hl := Real.log_le_log (Real.exp_pos _) hl'
  rw [Real.log_mul hN.ne' (Real.exp_pos _).ne',Real.log_exp] at hu
  rw [Real.log_exp] at hl
  change |Real.log Z| ≤ (D+|Real.log N|)*(1+‖e‖)
  apply abs_le.2
  have hextra := mul_nonneg (abs_nonneg (Real.log N)) (norm_nonneg e)
  dsimp [A] at hu hl
  constructor
  · linarith [abs_nonneg (Real.log N)]
  · linarith [le_abs_self (Real.log N),abs_nonneg (Real.log N)]

end ParameterFiniteLog
end SK.Analytic

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

instance fiberGaussian_probability : (n : ℕ) → (x : ℝ) → IsProbabilityMeasure (fiberGaussian n x)
  | 0, x => inferInstanceAs (IsProbabilityMeasure (Measure.dirac x))
  | n+1, x => by
      let := fiberGaussian_probability n x
      exact inferInstanceAs (IsProbabilityMeasure ((fiberGaussian n x).prod (gaussianReal 0 1)))

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
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def hierarchyLevel : (n : ℕ) → (Fin n → ℝ) → (ParameterSpace n → ℝ) →
    Fin (n+1) → ParameterSpace n → ℝ
  | 0,_,f,_ => f
  | n+1,m,f,j => Fin.lastCases f (fun i z =>
      hierarchyLevel n (fun i => m i.castSucc) (gaussianStep (m (Fin.last n)) f) i z.1) j

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
def disorderPairLaw (n : ℕ) : Measure (Disorder n × Disorder n) :=
  (disorderLaw n).prod (disorderLaw n)

instance disorderPairLaw_probability (n : ℕ) : IsProbabilityMeasure (disorderPairLaw n) := by
  unfold disorderPairLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

def directionalEnergy {n : ℕ} (β : ℝ) (J K : Disorder n) : ℝ :=
  β * ∑ x : Config n, gibbs β J x * hamiltonian K x

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
def logPartition {n : ℕ} (β : ℝ) (J : Disorder n) : ℝ := Real.log (partition β J)

def rotationIntegrand {n : ℕ} (β θ ℓ : ℝ) (s : ℝ) (p : Disorder n × Disorder n) : ℝ :=
  Real.exp (ℓ * θ * directionalEnergy β (rotateDisorder (θ * s) p).1
    (rotateDisorder (θ * s) p).2)

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

def gaugeConfigEquiv {n : ℕ} (v : Config n) : Config n ≃ Config n :=
  { toFun := gaugeConfig v
    invFun := gaugeConfig v
    left_inv := gaugeConfig_involutive v
    right_inv := gaugeConfig_involutive v }

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

def monomialSign {N : ℕ} (v : Config N) (I : Finset (Fin N)) : Bool :=
  decide (spinMonomial v I = -1)

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
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_SKBlockCoordinates
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

def skInteraction (N : ℕ) (i : Fin (Fintype.card (Edge N))) : Finset (Fin N) :=
  let e := (Fintype.equivFin (Edge N)).symm i
  {e.val.1,e.val.2}

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

def quenchedPressure (β : ℝ) (N : ℕ) : ℝ :=
  (∫ J, logPartition β J ∂disorderLaw N)/(N:ℝ)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_EnergyTail
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

def gibbsEnergyTail {N : ℕ} (β e : ℝ) (J : Disorder N) : ℝ :=
  ∑ s : Config N, if (N:ℝ)*e < hamiltonian J s then gibbs β J s else 0

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_RestrictedConcentration
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

def replicaGibbsMass {n d : ℕ} (β : ℝ) (J : Disorder n) (S : Finset (ReplicaConfig n d)) : ℝ :=
  ∑ s ∈ S, ∏ a, gibbs β J (s a)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_PressureGapFiniteInf
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

def restrictedPressure {n d : ℕ} (β : ℝ) (S : Finset (ReplicaConfig n d)) : ℝ :=
  (∫ J, restrictedLogPartition β S J ∂disorderLaw n)/(n:ℝ)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_HeatBathChoice
attribute [-instance] _root_.OAI.SK.disorderLaw_probability _root_.OAI.SK.disorderPairLaw_probability
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

theorem siteChoice_fiber {n : ℕ} (β : ℝ) (J : Disorder n) (x y : Config n) (i : Fin n) :
    (∑ b : Bool, if Function.update x i b = y then siteChoice β J x i b else 0) =
      if Function.update x i (y i) = y then siteChoice β J x i (y i) else 0 := by
  classical
  apply Finset.sum_eq_single (y i)
  · intro b _ hbi
    have H : Function.update x i b ≠ y := by
      intro he
      have he' := congrFun he i
      exact hbi (by simpa only [Function.update_self] using he')
    simp only [ite_eq_right H]
  · simp

theorem heatBath_eq_siteChoice {n : ℕ} (β : ℝ) (J : Disorder n) (x y : Config n) :
    heatBath β J x y = (∑ i : Fin n, ∑ b : Bool,
      if Function.update x i b = y then siteChoice β J x i b else 0)/(n:ℝ) := by
  unfold heatBath
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [siteChoice_fiber]
  rfl

theorem heatBath_nonneg {n : ℕ} (β : ℝ) (J : Disorder n) (x y : Config n) :
    0 ≤ heatBath β J x y := by
  rw [heatBath_eq_siteChoice]
  apply div_nonneg _ (Nat.cast_nonneg n)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro b _
  split_ifs
  · exact (siteChoice_pos β J x i b).le
  · rfl

theorem heatBath_sum {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n) (x : Config n) :
    ∑ y : Config n, heatBath β J x y = 1 := by
  classical
  simp only [heatBath_eq_siteChoice]
  rw [← Finset.sum_div,Finset.sum_comm]
  have HS : (∑ i : Fin n, ∑ y : Config n, ∑ b : Bool,
      if Function.update x i b = y then siteChoice β J x i b else 0) = (n:ℝ) := by
    calc
      _ = ∑ i : Fin n, ∑ b : Bool, siteChoice β J x i b := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        simp
      _ = _ := by simp only [siteChoice_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
        nsmul_eq_mul,mul_one]
  rw [HS]
  exact div_self (by exact_mod_cast hn.ne')

end SK.Analytic

end
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

def vectorStep (m : ℝ) (v : E) (f : E → ℝ) : E → ℝ :=
  gaussianStep m (fun z : E × ℝ => f (z.1+z.2 • v))

def vectorHierarchy : (n : ℕ) → (Fin n → ℝ) → (Fin n → E) → (E → ℝ) → E → ℝ
  | 0,_,_,f => f
  | n+1,m,v,f => vectorHierarchy n (fun i => m i.castSucc) (fun i => v i.castSucc)
      (vectorStep (m (Fin.last n)) (v (Fin.last n)) f)

end Vector

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

def productMass : ProductIncrement (E:=E) (F:=F) → ℝ
  | .inl p => p.1
  | .inr p => p.1/2

def productVector : ProductIncrement (E:=E) (F:=F) → E × F
  | .inl p => (p.2,0)
  | .inr p => (0,p.2)

def productLeft (l : List (ProductIncrement (E:=E) (F:=F))) : List (ℝ × E) :=
  l.filterMap (fun p => match p with | .inl q => some q | .inr _ => none)

def productRight (l : List (ProductIncrement (E:=E) (F:=F))) : List (ℝ × F) :=
  l.filterMap (fun p => match p with | .inl _ => none | .inr q => some q)

end Vector

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_MatrixSKCovariance
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

def matrixSKObservables {S : Type} (N d : ℕ) (β : ℝ) (e : S → Fin N → Config d) :
    Fin (Fintype.card (Edge N)) → S → ℝ := fun u s =>
  (β/Real.sqrt (N:ℝ))*∑ a,
    spin (e s ((Fintype.equivFin (Edge N)).symm u).val.1 a)*
      spin (e s ((Fintype.equivFin (Edge N)).symm u).val.2 a)

attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

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

def matrixSKLogPartition (N d : ℕ) (β : ℝ) (e : S → Fin N → Config d) (J : Disorder N) : ℝ :=
  Real.log (∑ s, Real.exp (β*∑ a, hamiltonian J (fun i => e s i a)))

instance matrixStatesFintype (N d : ℕ) (D : Fin d → Fin d → ℝ) :
    Fintype (MatrixStates N d D) := by
  classical
  unfold MatrixStates
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

def matrixConstrainedPressure (N d : ℕ) (β : ℝ) (D : Fin d → Fin d → ℝ) : ℝ :=
  (∫ J, Real.log (∑ s : MatrixStates N d D,
    Real.exp (β*∑ a, hamiltonian J (fun i => s.val i a))) ∂disorderLaw N)/(N:ℝ)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_VectorBlocks
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
section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def vectorBlockHierarchy (r : ℕ) : (n : ℕ) → (Fin n → ℝ) → (Fin n → Fin r → E) → (E → ℝ) → E → ℝ
  | 0,_,_,f => f
  | n+1,m,v,f => vectorBlockHierarchy r n (fun i => m i.castSucc) (fun i => v i.castSucc)
      (vectorHierarchy r (fun _ => m (Fin.last n)) (v (Fin.last n)) f)

end

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

def matrixChainPenalty {d : ℕ} (l : List (ℝ × (Fin d → ℝ))) (Q : Fin d → Fin d → ℝ) : ℝ :=
  chainPotentialPenalty (matrixSquare d) (l.map (fun p => (p.1,rankOneMatrix p.2))) Q

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

def weightedVariancePenalty (l : List (ℝ × (ℝ × ℝ))) (G : ℝ) : ℝ :=
  chainPotentialPenalty (fun x : ℝ => x^2) (l.map (fun p => (p.1,p.2.2^2))) G

@[simp] theorem matrixChainPenalty_nil {d : ℕ} (Q : Fin d → Fin d → ℝ) :
    matrixChainPenalty [] Q=0 := rfl
@[simp] theorem matrixChainPenalty_cons {d : ℕ} (p : ℝ × (Fin d → ℝ)) (l : List (ℝ × (Fin d → ℝ))) (Q : Fin d → Fin d → ℝ) :
    matrixChainPenalty (p::l) Q=p.1*(matrixSquare d (Q+rankOneMatrix p.2)-matrixSquare d Q)+
      matrixChainPenalty l (Q+rankOneMatrix p.2) := rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_ProductMerge
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
section Vector
variable {E F : Type}

def mergedProductBranches (l : List (ℝ × E)) (r : List (ℝ × F)) : List (ProductIncrement (E:=E) (F:=F)) :=
  (l.map Sum.inl).merge (r.map Sum.inr) (fun p q => decide (productMass p ≤ productMass q))

end Vector
end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ProductBranchMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SK.Analytic
section Map
variable {E F E' F' : Type}

def mapProductIncrement (f : E → E') (g : F → F') :
    ProductIncrement (E:=E) (F:=F) → ProductIncrement (E:=E') (F:=F') :=
  Sum.map (fun p => (p.1,f p.2)) (fun p => (p.1,g p.2))

@[simp] theorem productMass_map (f : E → E') (g : F → F') (p : ProductIncrement (E:=E) (F:=F)) :
    productMass (mapProductIncrement f g p)=productMass p := by cases p <;> rfl

end Map

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

@[simp] theorem weightedMean_scale (β : ℝ) (w : List (ℝ × (ℝ × ℝ))) :
    weightedMean (scaleIncrementChain β w)=β^2*weightedMean w := by
  induction w with
  | nil => simp [weightedMean,scaleIncrementChain]
  | cons p w ih =>
    change β*p.2.2*(β*p.2.1)*p.1+weightedMean (scaleIncrementChain β w)=β^2*(p.2.2*p.2.1*p.1+weightedMean w)
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

def narrowMiddleVector (δ : ℝ) : NarrowMiddleIncrement → Fin 3 → ℝ
  | .inl p => ![p.2.1,δ*p.2.2,-δ*p.2.2]
  | .inr p => ![0,p.2.1+δ*p.2.2,p.2.1-δ*p.2.2]

def narrowMiddleSchedule (δ : ℝ) (l : List NarrowMiddleIncrement) : List (ℝ × (Fin 3 → ℝ)) :=
  l.map (fun p => (productMass p,narrowMiddleVector δ p))

def narrowMiddleNoise : NarrowMiddleIncrement → ℝ
  | .inl p => p.2.2
  | .inr p => p.2.2

def narrowNoisePenalty (l : List NarrowMiddleIncrement) (K : ℝ) : ℝ :=
  chainPotentialPenalty (fun x : ℝ => x^2) (l.map (fun p => (productMass p,(narrowMiddleNoise p)^2))) K

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

def narrowRetainedCommon (c : List (ℝ × (ℝ × ℝ))) : List (ℝ × NarrowRetainedState) :=
  c.map (fun p => (p.1/3,((p.2.1,0),(p.2.1,p.2.2))))

def narrowRetainedMiddle (l : List NarrowMiddleIncrement) : List (ℝ × NarrowRetainedState) :=
  l.map (fun p => (productMass p,productVector p))

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowRetainedExpansion
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

def narrowToTriple : NarrowRetainedState →L[ℝ] TripleRetainedState :=
  (((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ))).prod
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ))+
      (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ)))).prod
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ)))

@[simp] theorem narrowToTriple_apply (p : NarrowRetainedState) :
    narrowToTriple p=((p.1.1,p.1.2+p.2.2),p.2.1) := rfl

def narrowRetainedEmbedding (δ : ℝ) : NarrowRetainedState →L[ℝ] (Fin 3 → ℝ) :=
  (tripleRetainedEmbedding δ).comp narrowToTriple

@[simp] theorem narrowRetainedEmbedding_apply (δ : ℝ) (p : NarrowRetainedState) :
    narrowRetainedEmbedding δ p= ![p.1.1,p.2.1+δ*(p.1.2+p.2.2),p.2.1-δ*(p.1.2+p.2.2)] := by
  simp [narrowRetainedEmbedding,tripleRetainedEmbedding_apply,narrowToTriple_apply]

def narrowRetainedPrefix (c v w : List (ℝ × (ℝ × ℝ))) : List (ℝ × NarrowRetainedState) :=
  narrowRetainedCommon c++narrowRetainedMiddle (mergedProductBranches v w)

def narrowSchedule (δ : ℝ) (c v w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) : List (ℝ × (Fin 3 → ℝ)) :=
  narrowCommonSchedule δ c++narrowMiddleSchedule δ (mergedProductBranches v w)++tripleTailSchedule t

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowRetainedStats
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

def narrowVariance (c v w : List (ℝ × (ℝ × ℝ))) := weightedVariance c+weightedVariance v+weightedVariance w
def narrowAbsCross (c v w : List (ℝ × (ℝ × ℝ))) := 3*weightedAbsCross c+weightedAbsCross v+2*weightedAbsCross w

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowScheduleEndpoint
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

def narrowCrossPenalty (c v w : List (ℝ × (ℝ × ℝ))) : ℝ :=
  weightedCrossPenalty c 0+weightedCrossPenalty v (weightedCross c)+weightedCrossPenalty w (weightedCross c)

def narrowQuarticPenalty (c v w : List (ℝ × (ℝ × ℝ))) : ℝ :=
  weightedVariancePenalty c 0/3+narrowNoisePenalty (mergedProductBranches v w) (weightedVariance c)

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

theorem partitionTimeChain_duration (n : ℕ) (q : Fin (n+1) → ℝ) (hq : Monotone q)
    (m : Fin n → ℝ) : (chainDuration (partitionTimeChain n q hq m):ℝ)=q (Fin.last n)-q 0 := by
  simp only [partitionTimeChain,chainDuration,List.map_ofFn,List.sum_ofFn,
    NNReal.coe_sum,NNReal.coe_mk,Function.comp_apply,Finset.sum_sub_distrib]
  have H₁ := Fin.sum_univ_succ q
  have H₂ := Fin.sum_univ_castSucc q
  linarith

theorem partitionTimeChain_models (n : ℕ) (q : Fin (n+1) → ℝ) (hq : Monotone q)
    (m : Fin n → ℝ) {α : ℝ → ℝ}
    (hc : ∀ i : Fin n, ∀ z∈Ico (q i.castSucc) (q i.succ), α z=m i) :
    TimeChainModels α (q 0) (partitionTimeChain n q hq m) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    simp only [partitionTimeChain,List.ofFn_succ,TimeChainModels,NNReal.coe_mk]
    constructor
    · intro z hz
      apply hc 0 z
      simpa only [Fin.castSucc_zero,Fin.succ_zero_eq_one,add_sub_cancel] using hz
    · have H := ih (fun i => q i.succ) (fun _ _ h => hq (Fin.succ_le_succ_iff.mpr h))
        (fun i => m i.succ) (fun i z hz => hc i.succ z hz)
      simpa only [partitionTimeChain,Fin.succ_zero_eq_one,Fin.castSucc_zero,Fin.succ_castSucc,add_sub_cancel] using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_QuantileChain
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

theorem quantileCDF_monotone (k : ℕ) (Q : Fin (k+1) → ℝ) : Monotone (quantileCDF k Q) := by
  intro s t hst
  simp only [quantileCDF_formula]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : Q j ≤ s
  · simp only [ite_eq_left hj,ite_eq_left (hj.trans hst),le_refl]
  · simp only [ite_eq_right hj]
    split_ifs <;> positivity

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

theorem quantileCDF_of_last_le {k : ℕ} (Q : Fin (k+1) → ℝ) (hQ : Monotone Q)
    {z : ℝ} (hz : Q (Fin.last k) ≤ z) : quantileCDF k Q z=1 := by
  rw [quantileCDF_formula]
  simp only [ite_eq_left ((hQ (Fin.le_last _)).trans hz),uniformAtom_sum]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFUniformQuantiles
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

theorem uniformCDFQuantiles_L1_tendsto (α : StieltjesFunction ℝ)
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hα1 : α 1=1) :
    Tendsto (fun k => ∫ x in Icc (0:ℝ) 1,
      |quantileCDF k (uniformCDFQuantiles k α) x-α x|) atTop (𝓝 0) := by
  refine squeeze_zero (g := fun k : ℕ => ((k+1:ℕ):ℝ)⁻¹)
    (fun _ => integral_nonneg (fun _ => abs_nonneg _)) (fun k => ?_) ?_
  · have hi : IntegrableOn (fun x => |quantileCDF k (uniformCDFQuantiles k α) x-α x|) (Icc (0:ℝ) 1) :=
      ((MonotoneOn.integrableOn_isCompact isCompact_Icc ((quantileCDF_monotone k (uniformCDFQuantiles k α)).monotoneOn _)).sub
        (MonotoneOn.integrableOn_isCompact isCompact_Icc (α.mono.monotoneOn _))).abs
    have H := setIntegral_mono_on hi
      (integrableOn_const (s := Icc (0:ℝ) 1) (μ := volume) (C := ((k+1:ℕ):ℝ)⁻¹) (by simp)) measurableSet_Icc
      (fun x hx => quantileCDF_uniformCDFQuantiles_error k α hα hα1 hx)
    simpa using H
  · simpa only [Nat.cast_add,Nat.cast_one,one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowRetainedCommon
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

def narrowCommonEmbedding : (ℝ × ℝ) →L[ℝ] NarrowRetainedState :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod 0).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))

@[simp] theorem narrowCommonEmbedding_apply (p : ℝ × ℝ) : narrowCommonEmbedding p=((p.1,0),p) := rfl

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

def weightedMarker : (ℝ × ℝ) →L[ℝ] MarkedWeightedState :=
  (ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod (ContinuousLinearMap.fst ℝ ℝ ℝ)

@[simp] theorem weightedMarker_apply (p : ℝ × ℝ) : weightedMarker p=(p,p.1) := rfl

def markedWeightedChain (c w : List (ℝ × (ℝ × ℝ))) : List (ℝ × MarkedWeightedState) :=
  c.map (fun p => (p.1,weightedMarker p.2))++w.map (fun p => (p.1,(p.2,0)))

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_WeightedMarkedIntegral
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

def markedScalarVector (n : ℕ) (v a : Fin n → ℝ) (j : Fin (n+1)) (i : Fin n) : MarkedWeightedState :=
  ((v i,a i),scalarPrefixVector n v j i)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarListBounds
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

def weightedMomentBound (w : List (ℝ × (ℝ × ℝ))) : ℝ := 2*weightedVariance w+(2*weightedAbsCross w)^2

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleScaleStats
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

@[simp] theorem rawVariance_scale (β : ℝ) (l : List (ℝ × ℝ)) :
    rawVariance (scaleIncrementChain β l)=β^2*rawVariance l := by
  induction l with
  | nil => simp [rawVariance,scaleIncrementChain]
  | cons p l ih =>
    change (β*p.2)^2+rawVariance (scaleIncrementChain β l)=β^2*(p.2^2+rawVariance l)
    rw [ih]; ring

@[simp] theorem rawArea_scale (β : ℝ) (l : List (ℝ × ℝ)) :
    rawArea (scaleIncrementChain β l)=β^2*rawArea l := by
  induction l with
  | nil => simp [rawArea,scaleIncrementChain]
  | cons p l ih =>
    change p.1*(β*p.2)^2+rawArea (scaleIncrementChain β l)=β^2*(p.1*p.2^2+rawArea l)
    rw [ih]; ring

@[simp] theorem weightedVariance_scale (β : ℝ) (w : List (ℝ × (ℝ × ℝ))) :
    weightedVariance (scaleIncrementChain β w)=β^2*weightedVariance w := by
  induction w with
  | nil => simp [weightedVariance,scaleIncrementChain]
  | cons p w ih =>
    change (β*p.2.2)^2+weightedVariance (scaleIncrementChain β w)=β^2*(p.2.2^2+weightedVariance w)
    rw [ih]; ring

@[simp] theorem weightedCross_scale (β : ℝ) (w : List (ℝ × (ℝ × ℝ))) :
    weightedCross (scaleIncrementChain β w)=β^2*weightedCross w := by
  induction w with
  | nil => simp [weightedCross,scaleIncrementChain]
  | cons p w ih =>
    change (β*p.2.1)*(β*p.2.2)+weightedCross (scaleIncrementChain β w)=β^2*(p.2.1*p.2.2+weightedCross w)
    rw [ih]; ring

@[simp] theorem weightedAbsCross_scale (β : ℝ) (w : List (ℝ × (ℝ × ℝ))) :
    weightedAbsCross (scaleIncrementChain β w)=β^2*weightedAbsCross w := by
  induction w with
  | nil => simp [weightedAbsCross,scaleIncrementChain]
  | cons p w ih =>
    change |β*p.2.2| * |β*p.2.1|+weightedAbsCross (scaleIncrementChain β w)=β^2*(|p.2.2| * |p.2.1|+weightedAbsCross w)
    rw [ih,abs_mul,abs_mul,← sq_abs β]; ring

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_FourBlockTent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SK.Analytic

abbrev fourBlockTent (κ : ℝ) (b l j k : List (ℝ × ℝ)) : List (ℝ × (ℝ × ℝ)) :=
  (zeroWeightChain b++constantWeightChain κ l)++(constantWeightChain (-κ) j++zeroWeightChain k)

@[simp] theorem fourBlockTent_length (κ : ℝ) (b l j k : List (ℝ × ℝ)) :
    (fourBlockTent κ b l j k).length=b.length+l.length+j.length+k.length := by
  simp only [fourBlockTent,zeroWeightChain,constantWeightChain,List.length_append,List.length_map]
  omega

abbrev fourBlockLeft (κ : ℝ) (b l j k : List (ℝ × ℝ)) : Fin ((fourBlockTent κ b l j k).length+1) :=
  ⟨b.length,by rw [fourBlockTent_length]; omega⟩
abbrev fourBlockMiddle (κ : ℝ) (b l j k : List (ℝ × ℝ)) : Fin ((fourBlockTent κ b l j k).length+1) :=
  ⟨b.length+l.length,by rw [fourBlockTent_length]; omega⟩
abbrev fourBlockRight (κ : ℝ) (b l j k : List (ℝ × ℝ)) : Fin ((fourBlockTent κ b l j k).length+1) :=
  ⟨b.length+l.length+j.length,by rw [fourBlockTent_length]; omega⟩

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_FourBlockQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Set
namespace SK.Analytic

abbrev fourBlockCommon (κ : ℝ) (b l : List (ℝ × ℝ)) := zeroWeightChain b++constantWeightChain κ l
abbrev fourBlockFuture (κ : ℝ) (j k : List (ℝ × ℝ)) := constantWeightChain κ j++zeroWeightChain k

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleDecoupling
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

def tripleCommonError (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) : ℝ :=
  2*weightedMomentBound w*((susceptibilityLipschitzConstant:ℝ)+2*Real.exp 2)*
    Real.sqrt (2*rawVariance c+4*(rawVariance c)^2)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_WeightedMoments
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

def weightedPartition {n : ℕ} (ν : Config n → ℝ) (b : ℝ) (G : Disorder n) : ℝ :=
  ∑ x : Config n, ν x * Real.exp (b * hamiltonian G x)

def weightedOverlapMass {n : ℕ} (ν : Config n → ℝ) (q : ℝ) : ℝ :=
  ∑ x : Config n, ∑ y : Config n, if q ≤ |overlap x y| then ν x*ν y else 0

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

def pairSpinObservable (s : Config 2) : ℝ := spin (s 0)*spin (s 1)

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

def overlapCode {n : ℕ} (x y : Config n) : Fin (n+1) :=
  ⟨(Finset.univ.filter (fun i => x i=y i)).card,
    Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans_eq (by simp))⟩

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

def greedyRun {n : ℕ} (base : ℕ → Config n)
    (pick : ℕ → (ℕ → Config n) → ℕ → Config n)
    (x : ℕ → Config n) (r : ℕ → ℝ) (b : ℝ) (m : ℕ) : ℕ → GreedyRecord n
  | 0 => ⟨base,0,∅⟩
  | j+1 =>
    let s := greedyRun base pick x r b m j
    let w := pick j s.refs s.time
    ⟨Function.update s.refs j w,
      if j=0 then firstCrossing (fun k => overlap w (x k)) (r j) m
      else lastCrossing (fun k => overlap w (x k)) (r j) s.time,
      insert j (s.kept\s.kept.filter (fun i => b < |overlap (s.refs i) w|))⟩

def greedyReference {n : ℕ} (base : ℕ → Config n)
    (pick : ℕ → (ℕ → Config n) → ℕ → Config n)
    (x : ℕ → Config n) (r : ℕ → ℝ) (b : ℝ) (m j : ℕ) : Config n :=
  pick j (greedyRun base pick x r b m j).refs (greedyRun base pick x r b m j).time

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_OverlapPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators InnerProductSpace
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def spinUnitVector {n : ℕ} (x : Config n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => spin (x i)/Real.sqrt n)

end SK.Analytic

end
end

end OAI
end



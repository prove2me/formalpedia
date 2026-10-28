-- Prove2me | Definitions.Def_OAIQ070A000
-- name    : OAIQ070A000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T11:17:00.195994+00:00
-- url     : https://prove2.me/theorems/367f1c13-b8a9-4852-9f71-a3964ad9557a
-- title:
--   Definitions bundle OAIQ070A000 of the split of OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 169 declarations of OpenAI's Lean: 65 definitions, 5 inductive types or structures, 1 instance and 98 theorems. The definitions and types are `OAI.YauCounterexamples.AdmissiblePhaseHessian`, `OAI.YauCounterexamples.BoundedAlgebra.cubicPerturbation`, `OAI.YauCounterexamples.BoundedAlgebra.polynomial`, `OAI.YauCounterexamples.BoundedAlgebra.power`, `OAI.YauCounterexamples.BoundedAlgebra.remainder`, `OAI.YauCounterexamples.BoundedAlgebra.remainderConstant`, `OAI.YauCounterexamples.CoeffContinuous`, `OAI.YauCounterexamples.CompactMetricAtlas`, `OAI.YauCounterexamples.CompactMetricAtlas.ChartJetBound`, `OAI.YauCounterexamples.CompactMetricAtlas.H`, `OAI.YauCounterexamples.CompactMetricAtlas.H_nacg`, `OAI.YauCounterexamples.CompactMetricAtlas.H_ns`, `OAI.YauCounterexamples.CompactMetricAtlas.PatchCoefficients`, `OAI.YauCounterexamples.CompactMetricAtlas.VaryingPatchCoefficients`, `OAI.YauCounterexamples.CompactMetricAtlas.coveringRawTest`, `OAI.YauCounterexamples.CompactMetricAtlas.coveringRawTests`, `OAI.YauCounterexamples.CompactMetricAtlas.cutoffLocalization`, `OAI.YauCounterexamples.CompactMetricAtlas.highIndex`, `OAI.YauCounterexamples.CompactMetricAtlas.lift`, `OAI.YauCounterexamples.CompactMetricAtlas.localize`, `OAI.YauCounterexamples.CompactMetricAtlas.ofSmooth`, `OAI.YauCounterexamples.CompactMetricAtlas.p`, `OAI.YauCounterexamples.CompactMetricAtlas.representative`, `OAI.YauCounterexamples.CompactMetricAtlas.scalarChartSupport`, `OAI.YauCounterexamples.CompactMetricAtlas.smoothCutoffLocalization`, `OAI.YauCounterexamples.CompactMetricAtlas.χcoord`, `OAI.YauCounterexamples.CompactMetricAtlas.ψcoord`, `OAI.YauCounterexamples.FourierSobolevSpace`, `OAI.YauCounterexamples.LocalMetricInverse`, `OAI.YauCounterexamples.ManifoldSmoothFunctions`, `OAI.YauCounterexamples.ManifoldSobolev`, `OAI.YauCounterexamples.RealForm`, `OAI.YauCounterexamples.SchwartzWordBound`, `OAI.YauCounterexamples.StrictlyBelow`, `OAI.YauCounterexamples.affineSchwartz`, `OAI.YauCounterexamples.atlasSobolevLocalization`, `OAI.YauCounterexamples.basisWordEval`, `OAI.YauCounterexamples.boundedDistribution`, `OAI.YauCounterexamples.chartLift`, `OAI.YauCounterexamples.chartLiftSmoothLinear` and 30 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `SmoothYau_DifferentialEq_LocalDiffeomorphismDetNeZero`, `SmoothYau_Estimates_BasisWordEval`, `SmoothYau_Estimates_CoefficientPerturbationTendsto`, `SmoothYau_Estimates_CutoffPullbackSobolevBound`, `SmoothYau_Estimates_PullbackLintegral`, `SmoothYau_Estimates_RealValueCubic`, `SmoothYau_Estimates_VaryingPatchCoefficients`, `SmoothYau_Geometry_ContMDiffComplexMul`, `SmoothYau_Geometry_RealForm`, `SmoothYau_Limits_CutoffFactorCompactRaw`, `SmoothYau_Limits_LocalMetricInverse`, `SmoothYau_Smoothness_BoundedDegreeMonomials`, `SmoothYau_Smoothness_ChartDerivativeNeZeroTransfer`, `SmoothYau_Smoothness_ChartGradientProjectionSmooth`, `SmoothYau_Smoothness_ConstantComplexProductJetBound`, `SmoothYau_Smoothness_ContinuousSobolevFirstDerivative`, `SmoothYau_Smoothness_FlowInitialFderiv`, `SmoothYau_Smoothness_LocalIntegrationParts`, `SmoothYau_Smoothness_LpNormTwoBounds`, `SmoothYau_Smoothness_MomentBesselLp`, `SmoothYau_Smoothness_SobolevRepresentativeOrderCongr`, `SmoothYau_Spectrum_AnisotropicConstant`.
--
--   **Imports.** It imports the published bundle `Def_SmoothYau`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ070A005`, `OAIQ070A006` and `OAIQ070A007`; the statements `OAI_YauCounterexamples_CompactMetricAtlas_eventually_positive_factor_of_jets`, `OAI_YauCounterexamples_CompactMetricAtlas_eventually_product_positive_factor_of_eventual_jets`, `OAI.YauCounterexamples.CompactMetricAtlas.global_cutoff_raw_controls`, `OAI_YauCounterexamples_CompactMetricAtlas_represented_weighted_quintic_smooth`, `OAI.YauCounterexamples.nonempty_compactMetricAtlas` and `OAI_YauCounterexamples_nonempty_localMetricInverse`; the proofs of `OAI.YauCounterexamples.nodalMeasure_coordinates_lower_bound`, `OAI_YauCounterexamples_regular_quotient_at_zero`, `OAI.YauCounterexamples.spherical_cutoff_control_bounds`, `OAI.YauCounterexamples.three_cutoff_control_bounds` and `OAI_YauCounterexamples_three_regular_quotient_at_zero`.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 1581d4c

import Mathlib
import Definitions.Def_SmoothYau

section
-- module Solutions.OAIQ070_YAU.Compat
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
-- module Solutions.OAIQ070_YAU.SmoothYau_DifferentialEq_LocalDiffeomorphismDetNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory intervalIntegral
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in

lemma compact_jacobian_bound {K : Set E} (hK : IsCompact K) {φ : E → E}
    (hφ : ContDiff ℝ ∞ φ) (hn : ∀ x ∈ K, (fderiv ℝ φ x).det ≠ 0) :
    ∃ J : ℝ≥0, ∀ x ∈ K, 1 ≤ (J : ℝ≥0∞) * ENNReal.ofReal |(fderiv ℝ φ x).det| := by
  have hc : ContinuousOn (fun x => |(fderiv ℝ φ x).det|⁻¹) K := by
    apply ContinuousOn.inv₀
    · exact (ContinuousLinearMap.continuous_det.comp
        (hφ.continuous_fderiv (by simp))).abs.continuousOn
    · intro x hx
      simpa only [ne_eq, abs_eq_zero] using hn x hx
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨Real.toNNReal (|B| + 1), ?_⟩
  intro x hx
  have hpos : 0 < |(fderiv ℝ φ x).det| := abs_pos.mpr (hn x hx)
  have hh : |(fderiv ℝ φ x).det|⁻¹ ≤ |B| + 1 := by
    calc
      _ ≤ ‖|(fderiv ℝ φ x).det|⁻¹‖ := le_abs_self _
      _ ≤ B := hB x hx
      _ ≤ |B| + 1 := by linarith [le_abs_self B]
  have hr : 1 ≤ (|B| + 1) * |(fderiv ℝ φ x).det| := by
    have hm := mul_le_mul_of_nonneg_right hh hpos.le
    rwa [inv_mul_cancel₀ hpos.ne'] at hm
  rw [ENNReal.ofNNReal_toNNReal]
  have hh' := ENNReal.ofReal_le_ofReal hr
  simpa only [ENNReal.ofReal_one, ENNReal.ofReal_mul (by positivity : 0 ≤ |B| + 1)] using hh'

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_BasisWordEval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

def basisWordEval (b : Module.Basis ι ℝ E) (n : ℕ) :
    (E [×n]→L[ℝ] ℂ) →ₗ[ℝ] ((Fin n → ι) → ℂ) where
  toFun T w := T (fun i => b (w i))
  map_add' T U := by ext w; rfl
  map_smul' c T := by ext w; rfl

omit [Fintype ι] in
lemma basisWordEval_injective (b : Module.Basis ι ℝ E) (n : ℕ) :
    Function.Injective (basisWordEval b n) := by
  intro T U h
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ => b)
  intro w
  exact congrFun h w

theorem multilinear_norm_le_basis_sum (b : Module.Basis ι ℝ E) (n : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ T : E [×n]→L[ℝ] ℂ,
      ‖T‖ ≤ C * ∑ w : Fin n → ι,
        ‖T (fun i => b (w i))‖ := by
  classical
  let : FiniteDimensional ℝ (E [×n]→L[ℝ] ℂ) :=
    FiniteDimensional.of_injective (basisWordEval b n) (basisWordEval_injective b n)
  obtain ⟨K, hK, ha⟩ := (basisWordEval b n).injective_iff_antilipschitz.mp
    (basisWordEval_injective b n)
  refine ⟨K, hK, fun T => ?_⟩
  refine (ZeroHomClass.bound_of_antilipschitz (basisWordEval b n) ha T).trans ?_
  apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).2
  intro w
  exact Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ w)

end YauCounterexamples

open MeasureTheory Set
open scoped ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_AnisotropicConstant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
namespace YauCounterexamples

variable (E F : Type*)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

abbrev FourierSobolevSpace (_s : ℝ) := Lp F 2 (volume : Measure E)

def fourierSobolevDistribution (s : ℝ) : FourierSobolevSpace E F s →L[ℂ] 𝓢'(E, F) :=
  fourierInvCLM ℂ _ ∘L
    (smulLeftCLM F (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2)))) ∘L
    Lp.toTemperedDistributionCLM F volume 2

variable {E F}

lemma fourierSobolevDistribution_apply (s : ℝ) (u : FourierSobolevSpace E F s) :
    fourierSobolevDistribution E F s u =
      𝓕⁻ (smulLeftCLM F (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2)))
        (Lp.toTemperedDistribution u)) := rfl

lemma weighted_fourier_fourierSobolevDistribution (s : ℝ)
    (u : FourierSobolevSpace E F s) :
    smulLeftCLM F (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (s / 2)))
      (𝓕 (fourierSobolevDistribution E F s u)) =
        Lp.toTemperedDistribution u := by
  rw [fourierSobolevDistribution_apply, fourier_fourierInv_eq,
    smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
  have hw : (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2))) *
      (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (s / 2))) = fun _ => 1 := by
    ext x
    simp only [Pi.mul_apply]
    norm_cast
    rw [← Real.rpow_add (by positivity)]
    convert Real.rpow_zero _ using 2
    all_goals try with_reducible_and_instances rfl
    ring
  rw [hw, smulLeftCLM_const]
  simp

lemma fourierSobolevDistribution_injective (s : ℝ) :
    Function.Injective (fourierSobolevDistribution E F s) := by
  intro u v huv
  have h := congrArg
    (fun f : 𝓢'(E, F) => smulLeftCLM F
      (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (s / 2))) (𝓕 f)) huv
  simp only [weighted_fourier_fourierSobolevDistribution] at h
  exact LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot h

lemma norm_bounded_toLp_top_le (g : E →ᵇ ℂ) :
    ‖(g.memLp_top (μ := (volume : Measure E))).toLp g‖ ≤ ‖g‖ := by
  rw [Lp.norm_toLp]
  have h : eLpNorm (g : E → ℂ) ∞ (volume : Measure E) ≤ ENNReal.ofReal ‖g‖ := by
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall g.norm_coe_le_norm)
  exact (ENNReal.toReal_mono (by finiteness) h).trans_eq
    (ENNReal.toReal_ofReal (norm_nonneg g))

def sobolevBoundedMultiplier (s : ℝ) (g : E →ᵇ ℂ) :
    FourierSobolevSpace E F s →L[ℂ] FourierSobolevSpace E F s :=
  LinearMap.mkContinuous
    { toFun := fun u => (g.memLp_top (μ := volume)).toLp g • u
      map_add' := fun u v => Lp.add_smul _ u v
      map_smul' := fun c u => (Lp.smul_comm c _ u).symm }
    ‖g‖ (fun u => (Lp.norm_smul_le _ u).trans
      (mul_le_mul_of_nonneg_right (norm_bounded_toLp_top_le g) (norm_nonneg u)))

omit [CompleteSpace F] in
lemma norm_sobolevBoundedMultiplier_le (s : ℝ) (g : E →ᵇ ℂ) :
    ‖sobolevBoundedMultiplier (F := F) s g‖ ≤ ‖g‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

lemma sobolevBoundedMultiplier_distribution (s : ℝ) (g : E →ᵇ ℂ)
    (hg : (g : E → ℂ).HasTemperateGrowth) (u : FourierSobolevSpace E F s) :
    fourierSobolevDistribution E F s (sobolevBoundedMultiplier s g u) =
      fourierMultiplierCLM F g (fourierSobolevDistribution E F s u) := by
  rw [fourierSobolevDistribution_apply, fourierMultiplierCLM_apply,
    fourierSobolevDistribution_apply, fourier_fourierInv_eq]
  change 𝓕⁻ (smulLeftCLM F _ (((g.memLp_top (μ := volume)).toLp g • u :
    Lp F 2 (volume : Measure E)) : 𝓢'(E, F))) = _
  rw [Lp.toTemperedDistribution_smul_eq hg,
    smulLeftCLM_smulLeftCLM_apply hg (by fun_prop),
    smulLeftCLM_smulLeftCLM_apply (by fun_prop) hg]
  rw [mul_comm]

lemma besselPotential_fourierSobolevDistribution (s t : ℝ)
    (u : FourierSobolevSpace E F s) :
    besselPotential E F t (fourierSobolevDistribution E F s u) =
      fourierSobolevDistribution E F (s - t) u := by
  rw [besselPotential, fourierMultiplierCLM_apply, fourierSobolevDistribution_apply,
    fourier_fourierInv_eq, fourierSobolevDistribution_apply,
    smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
  congr 3
  ext x
  simp only [Pi.mul_apply]
  norm_cast
  rw [← Real.rpow_add (by positivity)]
  congr 1
  ring

omit [CompleteSpace F] in
lemma quadraticMultiplier_eq (α : ℝ) (f : 𝓢'(E, F)) :
    fourierMultiplierCLM F (fun x : E => Complex.ofReal (α + ‖x‖ ^ 2)) f =
      α • f - ((2 * Real.pi) ^ 2 : ℝ)⁻¹ • Δ f := by
  rw [laplacian_eq_fourierMultiplierCLM, smul_smul,
    mul_neg, inv_mul_cancel₀ (pow_ne_zero _ (mul_ne_zero (by norm_num) Real.pi_ne_zero)),
    neg_one_smul, sub_neg_eq_add]
  have heq : (fun x : E => Complex.ofReal (α + ‖x‖ ^ 2)) =
      (fun _ => Complex.ofReal α) + (fun x => Complex.ofReal (‖x‖ ^ 2)) := by
    ext x
    simp
  rw [heq, fourierMultiplierCLM_apply, smulLeftCLM_add (by fun_prop) (by fun_prop)]
  simp only [fourierInv_add, fourierMultiplierCLM_apply, add_apply,
    smulLeftCLM_const]
  rw [fourierInv_smul, fourierInv_fourier_eq, Complex.coe_smul]

end YauCounterexamples

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff

end

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
namespace YauCounterexamples
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def sobolevInclusionSymbol (s t : ℝ) (h : t ≤ s) : E →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ ((t - s) / 2)))
    (by have hh : (fun x : E => Complex.ofReal
          ((1 + ‖x‖ ^ 2) ^ ((t - s) / 2))).HasTemperateGrowth := by fun_prop
        exact hh.1.continuous) 1 (by
      intro x
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by simp) (by linarith))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma sobolevInclusionSymbol_hasTemperateGrowth (s t : ℝ) (h : t ≤ s) :
    (sobolevInclusionSymbol (E := E) s t h : E → ℂ).HasTemperateGrowth := by
  change (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ ((t - s) / 2))).HasTemperateGrowth
  fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma norm_sobolevInclusionSymbol_le (s t : ℝ) (h : t ≤ s) :
    ‖sobolevInclusionSymbol (E := E) s t h‖ ≤ 1 := by
  rw [BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 1)]
  intro x
  change ‖Complex.ofReal ((1 + ‖x‖ ^ 2) ^ ((t - s) / 2))‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by simp) (by linarith)

def sobolevInclusion (s t : ℝ) (h : t ≤ s) :
    FourierSobolevSpace E F s →L[ℂ] FourierSobolevSpace E F t :=
  sobolevBoundedMultiplier s (sobolevInclusionSymbol s t h)

omit [CompleteSpace F] in
lemma norm_sobolevInclusion_le (s t : ℝ) (h : t ≤ s) :
    ‖sobolevInclusion (E := E) (F := F) s t h‖ ≤ 1 :=
  (norm_sobolevBoundedMultiplier_le _ _).trans (norm_sobolevInclusionSymbol_le s t h)

lemma sobolevInclusion_distribution (s t : ℝ) (h : t ≤ s)
    (u : FourierSobolevSpace E F s) :
    fourierSobolevDistribution E F t (sobolevInclusion s t h u) =
      fourierSobolevDistribution E F s u := by
  change fourierSobolevDistribution E F t
    (sobolevBoundedMultiplier t (sobolevInclusionSymbol s t h) u) = _
  rw [sobolevBoundedMultiplier_distribution _ _ (sobolevInclusionSymbol_hasTemperateGrowth s t h),
    fourierMultiplierCLM_apply, fourierSobolevDistribution_apply, fourier_fourierInv_eq,
    fourierSobolevDistribution_apply,
    smulLeftCLM_smulLeftCLM_apply (by fun_prop) (sobolevInclusionSymbol_hasTemperateGrowth s t h)]
  congr 3
  ext x
  change Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-t / 2)) *
    Complex.ofReal ((1 + ‖x‖ ^ 2) ^ ((t - s) / 2)) =
      Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2))
  rw [← Complex.ofReal_mul, ← Real.rpow_add (by positivity)]
  congr 2
  ring

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_MomentBesselLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
namespace YauCounterexamples

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def boundedDistribution (f : E →ᵇ F) : 𝓢'(E, F) :=
  ((f.memLp_top (μ := volume)).toLp f : 𝓢'(E, F))

lemma boundedDistribution_apply (f : E →ᵇ F) (φ : 𝓢(E, ℂ)) :
    boundedDistribution f φ = ∫ x, φ x • f x := by
  rw [boundedDistribution, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [(f.memLp_top (μ := volume)).coeFn_toLp] with x hx
  rw [hx]

def inverseFourierL1 (v : Lp F 1 (volume : Measure E)) : E →ᵇ F :=
  (Real.Lp.fourierTransform v).compContinuous ⟨fun x => -x, continuous_neg⟩

omit [CompleteSpace F] in
lemma inverseFourierL1_apply (v : Lp F 1 (volume : Measure E)) (x : E) :
    inverseFourierL1 v x = 𝓕⁻ (v : E → F) x := by
  exact (Real.fourierInv_eq_fourier_neg _ _).symm

theorem inverseFourierL1_distribution (v : Lp F 1 (volume : Measure E)) :
    boundedDistribution (inverseFourierL1 v) = 𝓕⁻ (v : 𝓢'(E, F)) := by
  ext φ
  rw [boundedDistribution_apply, TemperedDistribution.fourierInv_apply,
    Lp.toTemperedDistribution_apply]
  simp only [inverseFourierL1_apply, SchwartzMap.fourierInv_coe]
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (μ := (volume : Measure E)) (ν := (volume : Measure E))
    (L := -innerₗ E) (f := (φ : E → ℂ)) (g := (v : E → F))
    Real.continuous_fourierChar (innerSL ℝ).continuous₂.neg φ.integrable
    (L1.integrable_coeFn v)
  have hflip : (-innerₗ E).flip = -innerₗ E := by
    ext x y
    exact congrArg Neg.neg (real_inner_comm y x).symm
  rw [hflip] at h
  exact h.symm

lemma memLp_bessel_weight {s : ℝ} (hs : Module.finrank ℝ E < 2 * s) :
    MemLp (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ (-s / 2)) 2 := by
  have hgrowth : (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ (-s / 2)).HasTemperateGrowth := by
    fun_prop
  refine ⟨hgrowth.1.continuous.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  suffices h : ∫⁻ a : E, ENNReal.ofReal ‖(1 + ‖a‖ ^ 2) ^ (-s)‖ < ⊤ from by
    norm_cast
    simp_rw [ofReal_norm] at h
    simp_rw [← enorm_pow]
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext x
    rw [← Real.rpow_mul_natCast (by positivity)]
    congr 2
    ring
  apply ((integrable_rpow_neg_one_add_norm_sq hs).congr _).lintegral_lt_top
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_eq_self.mpr (by positivity)]
  congr
  ring

theorem boundedDistribution_injective :
    Function.Injective (boundedDistribution (E := E) (F := F)) := by
  intro u v huv
  have hi : Function.Injective
      (Lp.toTemperedDistributionCLM F (volume : Measure E) ∞) :=
    LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot
  have hLp : (u.memLp_top (μ := volume)).toLp u =
      (v.memLp_top (μ := volume)).toLp v := hi huv
  apply DFunLike.ext'
  apply Measure.eq_of_ae_eq (μ := (volume : Measure E)) _ u.continuous v.continuous
  exact ((u.memLp_top (μ := volume)).coeFn_toLp).symm.trans
    ((Filter.EventuallyEq.of_eq (congrArg (fun z : Lp F ∞ (volume : Measure E) =>
      (z : E → F)) hLp)).trans (v.memLp_top (μ := volume)).coeFn_toLp)

end YauCounterexamples

open MeasureTheory
open scoped ENNReal

end

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
namespace YauCounterexamples

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def sobolevWeight (s : ℝ) (x : E) : ℝ := (1 + ‖x‖ ^ 2) ^ (s / 2)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[fun_prop] lemma continuous_sobolevWeight (s : ℝ) :
    Continuous (sobolevWeight (E := E) s) := by
  unfold sobolevWeight
  exact (continuous_const.add (continuous_norm.pow 2)).rpow_const (fun x => Or.inl (by change 1 + ‖x‖ ^ 2 ≠ 0; positivity))

open scoped SchwartzMap

def weightedSchwartz (s : ℝ) (f : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x : E => Complex.ofReal (sobolevWeight s x)) f

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma weightedSchwartz_apply (s : ℝ) (f : 𝓢(E, ℂ)) (x : E) :
    weightedSchwartz s f x = Complex.ofReal (sobolevWeight s x) * f x := by
  unfold weightedSchwartz
  rw [SchwartzMap.smulLeftCLM_apply_apply]
  · rfl
  · unfold sobolevWeight
    fun_prop

open FourierTransform

end YauCounterexamples

end

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
namespace YauCounterexamples
open FourierTransform MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def schwartzToSobolev (s : ℝ) : 𝓢(E, ℂ) →L[ℂ] FourierSobolevSpace E ℂ s :=
  SchwartzMap.toLpCLM ℂ ℂ 2 volume ∘L
    SchwartzMap.smulLeftCLM ℂ (fun x : E => Complex.ofReal (sobolevWeight s x)) ∘L
    fourierCLM ℂ 𝓢(E, ℂ)

lemma schwartzToSobolev_apply (s : ℝ) (f : 𝓢(E, ℂ)) :
    schwartzToSobolev s f = (weightedSchwartz s (𝓕 f)).toLp 2 volume := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma weightedSchwartz_neg_cancel (s : ℝ) (f : 𝓢(E, ℂ)) :
    weightedSchwartz s (weightedSchwartz (-s) f) = f := by
  ext x
  rw [weightedSchwartz_apply, weightedSchwartz_apply, ← mul_assoc,
    ← Complex.ofReal_mul]
  have h : sobolevWeight s x * sobolevWeight (-s) x = 1 := by
    unfold sobolevWeight
    rw [← Real.rpow_add (by positivity)]
    convert Real.rpow_zero _ using 2
    all_goals try with_reducible_and_instances rfl
    ring
  rw [h, Complex.ofReal_one, one_mul]

lemma schwartz_smul_distribution (b : E → ℂ) (hb : b.HasTemperateGrowth)
    (f : 𝓢(E, ℂ)) :
    smulLeftCLM ℂ b (f : 𝓢'(E, ℂ)) =
      (SchwartzMap.smulLeftCLM ℂ b f : 𝓢'(E, ℂ)) := by
  ext φ
  simp only [smulLeftCLM_apply_apply, SchwartzMap.coe_apply]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [SchwartzMap.smulLeftCLM_apply_apply hb, smul_eq_mul]
  ring

lemma schwartzToSobolev_distribution (s : ℝ) (f : 𝓢(E, ℂ)) :
    fourierSobolevDistribution E ℂ s (schwartzToSobolev s f) = (f : 𝓢'(E, ℂ)) := by
  rw [schwartzToSobolev_apply, fourierSobolevDistribution_apply,
    Lp.toTemperedDistribution_toLp_eq]
  rw [schwartz_smul_distribution _ (by fun_prop)]
  change 𝓕⁻ ((weightedSchwartz (-s) (weightedSchwartz s (𝓕 f))) : 𝓢'(E, ℂ)) = _
  have h := weightedSchwartz_neg_cancel (-s) (𝓕 f)
  simp only [neg_neg] at h
  rw [h, TemperedDistribution.fourierInv_toTemperedDistributionCLM_eq, fourierInv_fourier_eq]

def sobolevAlgebraConstant (s : ℝ) : ℝ :=
  ((‖((4 : ℝ) ^ (s / 2))‖ₑ * 2 *
    eLpNorm (sobolevWeight (-s) : E → ℝ) 2 volume)).toReal

def inverseBesselLp {s : ℝ} (hs : Module.finrank ℝ E < 2 * s) :
    Lp ℂ 2 (volume : Measure E) :=
  (memLp_bessel_weight hs).ofReal.toLp
    (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2)))

def sobolevFourierL1 {s : ℝ} (hs : Module.finrank ℝ E < 2 * s) :
    FourierSobolevSpace E ℂ s →L[ℂ] Lp ℂ 1 (volume : Measure E) :=
  LinearMap.mkContinuous
    { toFun := fun u => (inverseBesselLp hs • u : Lp ℂ 1 (volume : Measure E))
      map_add' := fun u v => Lp.add_smul (r := 1) (inverseBesselLp hs) u v
      map_smul' := fun c u => (Lp.smul_comm (r := 1) c (inverseBesselLp hs) u).symm }
    ‖inverseBesselLp hs‖
    (fun u => Lp.norm_smul_le (r := 1) (inverseBesselLp hs) u)

def sobolevRepresentative {s : ℝ} (hs : Module.finrank ℝ E < 2 * s) :
    FourierSobolevSpace E ℂ s →L[ℂ] E →ᵇ ℂ :=
  Real.Lp.fourierTransformInvCLM E ℂ ∘L sobolevFourierL1 hs

lemma sobolevRepresentative_distribution {s : ℝ}
    (hs : Module.finrank ℝ E < 2 * s) (u : FourierSobolevSpace E ℂ s) :
    boundedDistribution (sobolevRepresentative hs u) = fourierSobolevDistribution E ℂ s u := by
  change boundedDistribution (inverseFourierL1 (inverseBesselLp hs • u)) = _
  rw [inverseFourierL1_distribution, inverseBesselLp,
    Lp.toTemperedDistribution_smul_eq (by fun_prop)]
  rfl

lemma boundedDistribution_schwartz (f : 𝓢(E, ℂ)) :
    boundedDistribution f.toBoundedContinuousFunction = (f : 𝓢'(E, ℂ)) := by
  ext φ
  rw [boundedDistribution_apply, SchwartzMap.coe_apply]
  rfl

lemma sobolevRepresentative_schwartz {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)
    (f : 𝓢(E, ℂ)) :
    sobolevRepresentative hs (schwartzToSobolev s f) = f.toBoundedContinuousFunction := by
  apply boundedDistribution_injective
  rw [sobolevRepresentative_distribution, schwartzToSobolev_distribution,
    boundedDistribution_schwartz]

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ContinuousSobolevFirstDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open scoped LineDeriv
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma normalized_derivative_symbol_bound (m x : E) :
    ‖Complex.ofReal (inner ℝ x m * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ))‖ ≤ ‖m‖ := by
  apply le_of_sq_le_sq _ (by positivity)
  simp only [Complex.ofReal_mul, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  have h₁ : |(1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ)| ^ 2 = (1 + ‖x‖ ^ 2)⁻¹ := by
    field_simp
    norm_cast
    rw [Real.rpow_neg (by positivity), sq_abs, inv_pow]
    field_simp
    calc
      _ = ((1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
        rw [← Real.rpow_mul (by positivity)]; simp
      _ = _ := by simp
  have h₂ : |inner ℝ x m| ^ 2 ≤ ‖m‖ ^ 2 * (1 + ‖x‖ ^ 2) := by
    grw [abs_real_inner_le_norm]
    rw [mul_pow, mul_comm]
    gcongr
    simp
  grw [h₁, h₂]
  apply le_of_eq
  field_simp

def normalizedDerivativeSymbol (m : E) : E →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => Complex.ofReal (inner ℝ x m * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ)))
    (by
      have h : (fun x : E => Complex.ofReal
        (inner ℝ x m * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ))).HasTemperateGrowth := by fun_prop
      exact h.1.continuous) ‖m‖ (normalized_derivative_symbol_bound m)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma norm_normalizedDerivativeSymbol_le (m : E) :
    ‖normalizedDerivativeSymbol m‖ ≤ ‖m‖ := by
  rw [BoundedContinuousFunction.norm_le (norm_nonneg _)]
  exact normalized_derivative_symbol_bound m

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma normalizedDerivativeSymbol_hasTemperateGrowth (m : E) :
    (normalizedDerivativeSymbol m : E → ℂ).HasTemperateGrowth := by
  change (fun x : E => Complex.ofReal
    (inner ℝ x m * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ))).HasTemperateGrowth
  fun_prop

def sobolevDerivative (s : ℝ) (m : E) :
    FourierSobolevSpace E F s →L[ℂ] FourierSobolevSpace E F (s - 1) :=
  (2 * Real.pi * Complex.I) • sobolevBoundedMultiplier s (normalizedDerivativeSymbol m)

lemma norm_sobolevDerivative_le (s : ℝ) (m : E) :
    ‖sobolevDerivative (F := F) s m‖ ≤ 2 * Real.pi * ‖m‖ := by
  unfold sobolevDerivative
  rw [norm_smul]
  have hc : ‖(2 : ℂ) * Real.pi * Complex.I‖ = 2 * Real.pi := by
    simp [Real.pi_nonneg]
  rw [hc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_sobolevBoundedMultiplier_le s _).trans (norm_normalizedDerivativeSymbol_le m)

lemma sobolevDerivative_distribution (s : ℝ) (m : E)
    (u : FourierSobolevSpace E F s) :
    fourierSobolevDistribution E F (s - 1) (sobolevDerivative s m u) =
      ∂_{m} (fourierSobolevDistribution E F s u) := by
  have h : besselPotential E F (-1) (∂_{m} (fourierSobolevDistribution E F s u)) =
      fourierSobolevDistribution E F s (sobolevDerivative s m u) := by
    rw [besselPotential_neg_one_lineDerivOp_eq]
    change _ = fourierSobolevDistribution E F s
      ((2 * Real.pi * Complex.I) • sobolevBoundedMultiplier s (normalizedDerivativeSymbol m) u)
    rw [map_smul, sobolevBoundedMultiplier_distribution _ _
      (normalizedDerivativeSymbol_hasTemperateGrowth m)]
    rfl
  have h' := (besselPotential_neg_apply_eq_iff 1 _ _).mp h
  rwa [besselPotential_fourierSobolevDistribution] at h'

lemma sobolevDerivative_bound (s : ℝ) (m : E) (u : FourierSobolevSpace E F s) :
    ‖sobolevDerivative s m u‖ ≤ 2 * Real.pi * ‖m‖ * ‖u‖ :=
  (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_sobolevDerivative_le s m) (norm_nonneg _))


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
open scoped SchwartzMap LineDeriv
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
lemma sobolevDerivative_schwartz (s : ℝ) (m : E) (f : 𝓢(E, ℂ)) :
    sobolevDerivative s m (schwartzToSobolev s f) = schwartzToSobolev (s - 1) (∂_{m} f) := by
  apply fourierSobolevDistribution_injective (s - 1)
  simp only [sobolevDerivative_distribution, schwartzToSobolev_distribution,
    TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq]


end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SobolevRepresentativeOrderCongr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped SchwartzMap BoundedContinuousFunction

section CompactDifferentialCoefficients
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

lemma contDiff_directional {χ : E → ℂ} (hχ : ContDiff ℝ ∞ χ) (b : E) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ χ x b) :=
  (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

end CompactDifferentialCoefficients

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def scalarAffineHomeomorph (p : E) (r : ℝ) (hr : r ≠ 0) : E ≃ₜ E where
  toFun x := p + r • x
  invFun x := r⁻¹ • (x - p)
  left_inv x := by simp [smul_smul, hr]
  right_inv x := by simp [smul_smul, hr]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

lemma hasCompactSupport_comp_scalarAffine {χ : E → ℂ} (hχ : HasCompactSupport χ)
    (p : E) (r : ℝ) (hr : r ≠ 0) : HasCompactSupport (fun x => χ (p + r • x)) :=
  hχ.comp_homeomorph (scalarAffineHomeomorph p r hr)

def affineSchwartz (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (p : E) (r : ℝ) (hr : r ≠ 0) : 𝓢(E, ℂ) :=
  (hasCompactSupport_comp_scalarAffine hχc p r hr).toSchwartzMap (hχ.comp (by fun_prop))
@[simp] lemma affineSchwartz_apply (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (p : E) (r : ℝ) (hr : r ≠ 0) (x : E) :
    affineSchwartz χ hχ hχc p r hr x = χ (p + r • x) := rfl



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_PullbackLintegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory
open MeasureTheory Set
open scoped ENNReal NNReal
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
  {K : Set E} {φ : E → E} {φ' : E → E →L[ℝ] E}

theorem pullback_lintegral_le (hK : MeasurableSet K)
    (hφ : ∀ x ∈ K, HasFDerivWithinAt φ (φ' x) K x) (hinj : InjOn φ K)
    (D : ℝ≥0) (hD : ∀ x ∈ K, 1 ≤ (D : ℝ≥0∞) * ENNReal.ofReal |(φ' x).det|)
    (g : E → ℝ≥0∞) :
    ∫⁻ x in K, g (φ x) ∂μ ≤ (D : ℝ≥0∞) * ∫⁻ y, g y ∂μ := by
  calc
    _ ≤ ∫⁻ x in K, (D : ℝ≥0∞) * (ENNReal.ofReal |(φ' x).det| * g (φ x)) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hK] with x hx
      simpa only [one_mul, mul_assoc] using mul_le_mul' (hD x hx) (le_refl (g (φ x)))
    _ = (D : ℝ≥0∞) * ∫⁻ x in K, ENNReal.ofReal |(φ' x).det| * g (φ x) ∂μ :=
      lintegral_const_mul' _ _ ENNReal.coe_ne_top
    _ = (D : ℝ≥0∞) * ∫⁻ y in φ '' K, g y ∂μ := by
      rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hK hφ hinj g]
    _ ≤ (D : ℝ≥0∞) * ∫⁻ y, g y ∂μ :=
      mul_le_mul' le_rfl (lintegral_mono' Measure.restrict_le_self le_rfl)

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_LpNormTwoBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open scoped LineDeriv
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma besselPotential_two_eq (f : 𝓢'(E, ℂ)) :
    besselPotential E ℂ 2 f = f - ((2 * Real.pi) ^ 2 : ℝ)⁻¹ • Δ f := by
  have h := quadraticMultiplier_eq (F := ℂ) 1 f
  simp only [one_smul] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [besselPotential, show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one]

def schwartzEllipticShift : 𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ) :=
  ContinuousLinearMap.id ℂ _ - ((2 * Real.pi) ^ 2 : ℝ)⁻¹ • LineDeriv.laplacianCLM ℂ E 𝓢(E, ℂ)

omit [MeasurableSpace E] [BorelSpace E] in
lemma schwartzEllipticShift_apply (f : 𝓢(E, ℂ)) :
    schwartzEllipticShift f = f - ((2 * Real.pi) ^ 2 : ℝ)⁻¹ • Δ f := by
  simp [schwartzEllipticShift, SchwartzMap.laplacianCLM_eq]

lemma schwartzEllipticShift_distribution (f : 𝓢(E, ℂ)) :
    (schwartzEllipticShift f : 𝓢'(E, ℂ)) = besselPotential E ℂ 2 (f : 𝓢'(E, ℂ)) := by
  rw [schwartzEllipticShift_apply, besselPotential_two_eq]
  simp

lemma schwartzToSobolev_shift (s : ℝ) (f : 𝓢(E, ℂ)) :
    schwartzToSobolev s (schwartzEllipticShift f) = schwartzToSobolev (s + 2) f := by
  apply fourierSobolevDistribution_injective s
  rw [schwartzToSobolev_distribution, schwartzEllipticShift_distribution]
  have h := besselPotential_fourierSobolevDistribution (s + 2) 2 (schwartzToSobolev (s + 2) f)
  rw [show s + 2 - 2 = s by ring] at h
  simpa only [schwartzToSobolev_distribution] using h

lemma schwartzToSobolev_zero (f : 𝓢(E, ℂ)) :
    schwartzToSobolev 0 f = 𝓕 (f.toLp 2 volume) := by
  rw [schwartzToSobolev_apply, SchwartzMap.toLp_fourier_eq]
  congr 1
  ext x
  simp [weightedSchwartz_apply, sobolevWeight]

lemma norm_schwartzToSobolev_zero (f : 𝓢(E, ℂ)) :
    ‖schwartzToSobolev 0 f‖ = ‖f.toLp 2 volume‖ := by
  rw [schwartzToSobolev_zero, Lp.norm_fourier_eq]

lemma sobolevInclusion_schwartz (s t : ℝ) (h : t ≤ s) (f : 𝓢(E, ℂ)) :
    sobolevInclusion s t h (schwartzToSobolev s f) = schwartzToSobolev t f := by
  apply fourierSobolevDistribution_injective t
  rw [sobolevInclusion_distribution, schwartzToSobolev_distribution, schwartzToSobolev_distribution]

lemma norm_schwartzToSobolev_mono (s t : ℝ) (h : t ≤ s) (f : 𝓢(E, ℂ)) :
    ‖schwartzToSobolev t f‖ ≤ ‖schwartzToSobolev s f‖ := by
  rw [← sobolevInclusion_schwartz s t h f]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (by simpa using mul_le_mul_of_nonneg_right
          (norm_sobolevInclusion_le (E := E) (F := ℂ) s t h) (norm_nonneg (schwartzToSobolev s f)))

lemma schwartz_derivative_norm_bound (s : ℝ) (v : E) (f : 𝓢(E, ℂ)) :
    ‖schwartzToSobolev (s - 1) (∂_{v} f)‖ ≤ 2 * Real.pi * ‖v‖ * ‖schwartzToSobolev s f‖ := by
  rw [← sobolevDerivative_schwartz]
  exact sobolevDerivative_bound s v _


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open scoped LineDeriv
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma norm_schwartz_word_bound (k : ℕ) (m : Fin k → E) (s : ℝ) (f : 𝓢(E, ℂ)) :
    ‖schwartzToSobolev s (∂^{m} f)‖ ≤
      (2 * Real.pi) ^ k * (∏ i, ‖m i‖) * ‖schwartzToSobolev (s + (k : ℝ)) f‖ := by
  induction k generalizing s with
  | zero =>
    simp only [LineDeriv.iteratedLineDerivOp_fin_zero, pow_zero, Fin.prod_univ_zero, one_mul]
    have he : s + (0 : ℕ) = s := by simp
    rw [he]
  | succ k ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left]
    have hd := schwartz_derivative_norm_bound (s + 1) (m 0) (∂^{Fin.tail m} f)
    rw [show s + 1 - 1 = s by ring] at hd
    have hi := ih (Fin.tail m) (s + 1)
    refine hd.trans ((mul_le_mul_of_nonneg_left hi (by positivity)).trans_eq ?_)
    rw [Fin.prod_univ_succ, pow_succ, Nat.cast_succ]
    have he : s + 1 + (k : ℝ) = s + ((k : ℝ) + 1) := by ring
    rw [he]
    simp only [Fin.tail_def]
    ring

lemma schwartz_word_L2_bound (k : ℕ) (m : Fin k → E) (s : ℝ) (h : (k : ℝ) ≤ s)
    (f : 𝓢(E, ℂ)) :
    ‖(∂^{m} f).toLp 2 volume‖ ≤
      (2 * Real.pi) ^ k * (∏ i, ‖m i‖) * ‖schwartzToSobolev s f‖ := by
  rw [← norm_schwartzToSobolev_zero]
  have hb := norm_schwartz_word_bound k m 0 f
  have he : (0 : ℝ) + (k : ℝ) = (k : ℝ) := zero_add _
  rw [he] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    (norm_schwartzToSobolev_mono s k h f) (by positivity))


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open scoped LineDeriv
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma norm_schwartz_shift_le (s : ℝ) (f : 𝓢(E, ℂ)) :
    ‖schwartzToSobolev (s + 2) f‖ ≤ ‖schwartzToSobolev s f‖ +
      ((2 * Real.pi) ^ 2 : ℝ)⁻¹ * ∑ i : Fin (Module.finrank ℝ E),
        ‖schwartzToSobolev s (∂_{stdOrthonormalBasis ℝ E i}
          (∂_{stdOrthonormalBasis ℝ E i} f))‖ := by
  rw [← schwartzToSobolev_shift, schwartzEllipticShift_apply,
    SchwartzMap.laplacian_eq_sum (stdOrthonormalBasis ℝ E)]
  let L := (schwartzToSobolev (E := E) s).restrictScalars ℝ
  change ‖L (f - ((2 * Real.pi) ^ 2 : ℝ)⁻¹ • ∑ i : Fin (Module.finrank ℝ E),
    ∂_{stdOrthonormalBasis ℝ E i} (∂_{stdOrthonormalBasis ℝ E i} f))‖ ≤
    ‖L f‖ + ((2 * Real.pi) ^ 2 : ℝ)⁻¹ * ∑ i : Fin (Module.finrank ℝ E),
      ‖L (∂_{stdOrthonormalBasis ℝ E i} (∂_{stdOrthonormalBasis ℝ E i} f))‖
  rw [map_sub, map_smul, map_sum]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity :
    0 ≤ ((2 * Real.pi) ^ 2 : ℝ)⁻¹)]
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (sq_nonneg (2 * Real.pi)))
  exact norm_sum_le _ _

def SchwartzWordBound (k : ℕ) (f : 𝓢(E, ℂ)) (B : ℝ) : Prop :=
  ∀ j, j ≤ k → ∀ w : Fin j → Fin (Module.finrank ℝ E),
    ‖(∂^{fun a => stdOrthonormalBasis ℝ E (w a)} f).toLp 2 volume‖ ≤ B

lemma SchwartzWordBound.mono {k l : ℕ} {f : 𝓢(E, ℂ)} {B : ℝ}
    (h : SchwartzWordBound k f B) (hle : l ≤ k) : SchwartzWordBound l f B :=
  fun j hj w => h j (hj.trans hle) w

lemma SchwartzWordBound.second {k : ℕ} {f : 𝓢(E, ℂ)} {B : ℝ}
    (h : SchwartzWordBound (k + 2) f B) (i : Fin (Module.finrank ℝ E)) :
    SchwartzWordBound k (∂_{stdOrthonormalBasis ℝ E i}
      (∂_{stdOrthonormalBasis ℝ E i} f)) B := by
  intro j hj w
  have hh := h (j + 2) (by omega) (Fin.snoc (Fin.snoc w i) i)
  change ‖(∂^{(stdOrthonormalBasis ℝ E) ∘ Fin.snoc (Fin.snoc w i) i} f).toLp 2 volume‖ ≤ B at hh
  simp only [Fin.comp_snoc, LineDeriv.iteratedLineDerivOp_succ_right,
    Fin.init_snoc, Fin.snoc_last] at hh
  exact hh

theorem sobolev_even_le_word_bound (k : ℕ) (f : 𝓢(E, ℂ)) (B : ℝ)
    (h : SchwartzWordBound (2 * k) f B) :
    ‖schwartzToSobolev (2 * (k : ℝ)) f‖ ≤
      (1 + ((2 * Real.pi) ^ 2 : ℝ)⁻¹ * Module.finrank ℝ E) ^ k * B := by
  induction k generalizing f with
  | zero =>
    have hh := h 0 (by omega) Fin.elim0
    rw [Nat.cast_zero, mul_zero, pow_zero, one_mul, norm_schwartzToSobolev_zero]
    exact hh
  | succ k ih =>
    have hf := ih f (h.mono (by omega))
    have hD : ∀ i : Fin (Module.finrank ℝ E),
        ‖schwartzToSobolev (2 * (k : ℝ)) (∂_{stdOrthonormalBasis ℝ E i}
          (∂_{stdOrthonormalBasis ℝ E i} f))‖ ≤
        (1 + ((2 * Real.pi) ^ 2 : ℝ)⁻¹ * Module.finrank ℝ E) ^ k * B := by
      intro i
      apply ih
      apply SchwartzWordBound.second
      exact h.mono (by omega)
    have hs := norm_schwartz_shift_le (2 * (k : ℝ)) f
    have he : 2 * (k : ℝ) + 2 = 2 * ((k + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [he] at hs
    refine hs.trans ((add_le_add hf
      (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hD i)) (by positivity))).trans_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pow_succ]
    ring


open MeasureTheory

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory
open MeasureTheory Set
open scoped ENNReal NNReal
open scoped LineDeriv NNReal ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma schwartz_word_eLpNorm_bound (j : ℕ) (w : Fin j → Fin (Module.finrank ℝ E))
    (s : ℝ) (hjs : (j : ℝ) ≤ s) (f : 𝓢(E, ℂ)) :
    eLpNorm ((∂^{fun a => stdOrthonormalBasis ℝ E (w a)} f : 𝓢(E, ℂ)) : E → ℂ) 2 volume ≤
      ENNReal.ofReal ((2 * Real.pi) ^ j * ‖schwartzToSobolev s f‖) := by
  rw [← Lp.enorm_toLp ((∂^{fun a => stdOrthonormalBasis ℝ E (w a)} f).memLp 2 volume),
    ← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  simpa only [SchwartzMap.toLp, OrthonormalBasis.norm_eq_one, Finset.prod_const_one, mul_one] using
    schwartz_word_L2_bound j (fun a => stdOrthonormalBasis ℝ E (w a)) s hjs f

theorem iteratedFDeriv_eLpNorm_bound (j : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (s : ℝ), (j : ℝ) ≤ s → ∀ f : 𝓢(E, ℂ),
      eLpNorm (iteratedFDeriv ℝ j f) 2 volume ≤
        ENNReal.ofReal (C * ‖schwartzToSobolev s f‖) := by
  classical
  obtain ⟨C, hC, hbound⟩ := multilinear_norm_le_basis_sum
    (stdOrthonormalBasis ℝ E).toBasis j
  refine ⟨C * (Fintype.card (Fin j → Fin (Module.finrank ℝ E)) + 1) *
    (2 * Real.pi) ^ j, by positivity, fun s hjs f => ?_⟩
  let W (w : Fin j → Fin (Module.finrank ℝ E)) : 𝓢(E, ℂ) :=
    ∂^{fun a => stdOrthonormalBasis ℝ E (w a)} f
  have hp (x : E) : ‖iteratedFDeriv ℝ j f x‖ ≤ C * ∑ w, ‖W w x‖ := by
    convert hbound (iteratedFDeriv ℝ j f x) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    apply Finset.sum_congr rfl
    intro w _
    simp only [W, SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
    rfl
  have hnorm : eLpNorm (iteratedFDeriv ℝ j f) 2 volume ≤
      ENNReal.ofReal C * ∑ w, eLpNorm (W w) 2 volume := by
    have hmeas : AEStronglyMeasurable (iteratedFDeriv ℝ j f) (volume : Measure E) :=
      ((f.smooth ⊤).continuous_iteratedFDeriv
        (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).aestronglyMeasurable
    calc
      _ ≤ eLpNorm (fun x => C * ∑ w, ‖W w x‖) 2 volume :=
        eLpNorm_mono_real hp
      _ = ENNReal.ofReal C * eLpNorm (∑ w, fun x => ‖W w x‖) 2 volume := by
        rw [show (fun x => C * ∑ w, ‖W w x‖) = C • (∑ w, fun x => ‖W w x‖) by
          ext x; simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul],
          eLpNorm_const_smul, Real.enorm_eq_ofReal hC.le]
      _ ≤ ENNReal.ofReal C * ∑ w, eLpNorm (W w) 2 volume := by
        apply mul_le_mul' le_rfl
        simpa only [eLpNorm_norm _] using eLpNorm_sum_le (hfs := fun _ _ => by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability)
          (s := Finset.univ) (μ := (volume : Measure E)) (p := 2)
          (f := fun w x => ‖W w x‖) (by norm_num)
  refine hnorm.trans ?_
  have hh := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ :
      Finset (Fin j → Fin (Module.finrank ℝ E)))) =>
    schwartz_word_eLpNorm_bound j w s hjs f)
  refine (mul_le_mul' le_rfl hh).trans ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul hC.le]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = C * (Fintype.card (Fin j → Fin (Module.finrank ℝ E)) : ℝ) *
      (2 * Real.pi) ^ j * ‖schwartzToSobolev s f‖ := by ring
    _ ≤ _ := by
      gcongr
      linarith


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory
open MeasureTheory Set
open scoped ENNReal NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def jetMajorant (N : ℕ) (f : E → ℂ) (x : E) : ℝ :=
  ∑ j ∈ Finset.range (N + 1), ‖iteratedFDeriv ℝ j f x‖

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma jetMajorant_nonneg (N : ℕ) (f : E → ℂ) (x : E) : 0 ≤ jetMajorant N f x :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma le_jetMajorant (N : ℕ) (f : E → ℂ) (x : E) (j : ℕ) (hj : j ≤ N) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ jetMajorant N f x :=
by
  unfold jetMajorant
  exact Finset.single_le_sum (f := fun i : ℕ => ‖iteratedFDeriv ℝ i f x‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_range.mpr (by omega : j < N + 1))

theorem jetMajorant_eLpNorm_bound (N : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (s : ℝ), (N : ℝ) ≤ s → ∀ f : 𝓢(E, ℂ),
      eLpNorm (jetMajorant N f) 2 volume ≤
        ENNReal.ofReal (C * ‖schwartzToSobolev s f‖) := by
  classical
  choose C hC hc using (fun j => iteratedFDeriv_eLpNorm_bound (E := E) j)
  have hsumpos : 0 ≤ ∑ j ∈ Finset.range (N + 1), C j :=
    Finset.sum_nonneg (fun j _ => (hC j).le)
  refine ⟨1 + ∑ j ∈ Finset.range (N + 1), C j, by linarith, fun s hs f => ?_⟩
  have hsum : eLpNorm (jetMajorant N f) 2 volume ≤
      ∑ j ∈ Finset.range (N + 1), ENNReal.ofReal (C j * ‖schwartzToSobolev s f‖) := by
    have hmeas (j : ℕ) : AEStronglyMeasurable
        (iteratedFDeriv ℝ j f) (volume : Measure E) :=
      (((f.smooth ⊤).continuous_iteratedFDeriv
        (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).aestronglyMeasurable)
    have hh := eLpNorm_sum_le (hfs := fun _ _ => by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (s := Finset.range (N + 1)) (μ := (volume : Measure E)) (p := 2)
      (f := fun j x => ‖iteratedFDeriv ℝ j f x‖) (by norm_num)
    have heq : (∑ j ∈ Finset.range (N + 1), fun x => ‖iteratedFDeriv ℝ j f x‖) =
        jetMajorant N f := by ext x; simp only [Finset.sum_apply, jetMajorant]
    rw [heq] at hh
    simp only [eLpNorm_norm _] at hh
    refine hh.trans (Finset.sum_le_sum ?_)
    intro j hj
    apply hc j s _ f
    have hjN : j ≤ N := by have := Finset.mem_range.mp hj; omega
    exact (show (j : ℝ) ≤ N by exact_mod_cast hjN).trans hs
  refine hsum.trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (hC j).le (norm_nonneg _)),
    ← Finset.sum_mul]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  linarith


open Function

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory
open MeasureTheory Set
open scoped ENNReal NNReal
open Function
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma compact_derivative_bound {K : Set E} (hK : IsCompact K)
    {f : E → F} (hf : ContDiff ℝ ∞ f) (N : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ j ≤ N, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ B := by
  classical
  have h (j : ℕ) := hK.exists_bound_of_continuousOn
    ((hf.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).continuousOn)
  choose c hc using h
  refine ⟨1 + ∑ j ∈ Finset.range (N + 1), |c j|,
    le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => abs_nonneg _)), ?_⟩
  intro j hj x hx
  calc
    _ ≤ c j := hc j x hx
    _ ≤ |c j| := le_abs_self _
    _ ≤ ∑ j ∈ Finset.range (N + 1), |c j| :=
      Finset.single_le_sum (f := fun i : ℕ => |c i|) (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (by omega : j < N + 1))
    _ ≤ _ := by linarith

lemma cutoff_comp_derivative_bound {K : Set E} (hK : IsCompact K)
    {η : E → ℂ} (hη : ContDiff ℝ ∞ η) {φ : E → E} (hφ : ContDiff ℝ ∞ φ)
    (N : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (f : E → ℂ), ContDiff ℝ ∞ f →
      ∀ n ≤ N, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ n (fun y => η y * f (φ y)) x‖ ≤
          C * jetMajorant N f (φ x) := by
  classical
  obtain ⟨B, hB, hb⟩ := compact_derivative_bound hK hη N
  obtain ⟨D, hD, hd⟩ := compact_derivative_bound hK hφ N
  let c (n : ℕ) : ℝ := ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) * B * (n - i).factorial * D ^ (n - i)
  have hc (n : ℕ) : 0 ≤ c n := by unfold c; positivity
  refine ⟨1 + ∑ n ∈ Finset.range (N + 1), c n, by positivity, ?_⟩
  intro f hf n hn x hx
  have H (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j (f ∘ φ) x‖ ≤
      j.factorial * jetMajorant N f (φ x) * D ^ j := by
    apply norm_iteratedFDeriv_comp_le hf hφ
      (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    · intro i hi
      exact le_jetMajorant N f (φ x) i (hi.trans hj)
    · intro i hi hi'
      exact (hd i (hi'.trans hj) x hx).trans (le_self_pow₀ hD (by omega))
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i η x‖ * ‖iteratedFDeriv ℝ (n - i) (f ∘ φ) x‖ :=
      norm_iteratedFDeriv_mul_le hη (hf.comp hφ) x
        (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * B *
        ((n - i).factorial * jetMajorant N f (φ x) * D ^ (n - i)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (hb i (by have := Finset.mem_range.mp hi; omega) x hx)
          (Nat.cast_nonneg _)
      · exact H (n - i) ((Nat.sub_le n i).trans hn)
      · exact norm_nonneg _
      · positivity
    _ = c n * jetMajorant N f (φ x) := by
      simp only [c, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ (1 + ∑ n ∈ Finset.range (N + 1), c n) * jetMajorant N f (φ x) := by
      apply mul_le_mul_of_nonneg_right _ (jetMajorant_nonneg ..)
      have hh := Finset.single_le_sum (fun j _ => hc j)
        (Finset.mem_range.mpr (by omega : n < N + 1))
      linarith


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory
open MeasureTheory Set
open scoped ENNReal NNReal
open Function
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def cutoffPullback (η : E → ℂ) (hηc : HasCompactSupport η) (hη : ContDiff ℝ ∞ η)
    (φ : E → E) (hφ : ContDiff ℝ ∞ φ) (f : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  (hηc.mul_right (f' := fun y => f (φ y))).toSchwartzMap (hη.mul ((f.smooth ⊤).comp hφ))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] lemma cutoffPullback_apply (η : E → ℂ) (hηc : HasCompactSupport η)
    (hη : ContDiff ℝ ∞ η) (φ : E → E) (hφ : ContDiff ℝ ∞ φ) (f : 𝓢(E, ℂ)) (x : E) :
    cutoffPullback η hηc hη φ hφ f x = η x * f (φ x) := rfl

lemma supported_pullback_eLpNorm_le {F : Type*} [NormedAddCommGroup F]
    {S : Set E} (hS : MeasurableSet S) {f : E → F} (hf : Function.support f ⊆ S)
    {φ : E → E} (hφ : ContDiff ℝ ∞ φ) (hinj : Set.InjOn φ S)
    (J : ℝ≥0) (hJ : ∀ x ∈ S, 1 ≤ (J : ℝ≥0∞) * ENNReal.ofReal |(fderiv ℝ φ x).det|)
    (g : E → ℝ) (A : ℝ) (hA : 0 ≤ A) (hb : ∀ x ∈ S, ‖f x‖ ≤ A * g (φ x)) :
    eLpNorm' f 2 volume ≤ ENNReal.ofReal A * ((J : ℝ≥0∞) ^ (1 / 2 : ℝ) * eLpNorm' g 2 volume) := by
  calc
    _ = eLpNorm' f 2 (volume.restrict S) := by
      simp only [eLpNorm'_eq_lintegral_enorm]
      congr 1
      symm
      apply setLIntegral_eq_of_support_subset
      intro x hx
      by_contra hnot
      have hzero : f x = 0 := by
        by_contra hnonzero
        exact hnot (hf hnonzero)
      simp [Function.mem_support, hzero] at hx
    _ ≤ eLpNorm' (fun x => A * g (φ x)) 2 (volume.restrict S) := by
      apply eLpNorm'_mono_ae (by norm_num)
      filter_upwards [ae_restrict_mem hS] with x hx
      exact (hb x hx).trans ((le_abs_self _).trans (Real.norm_eq_abs _).symm.le)
    _ = ENNReal.ofReal A * eLpNorm' (g ∘ φ) 2 (volume.restrict S) := by
      rw [show (fun x => A * g (φ x)) = A • (g ∘ φ) by rfl,
        eLpNorm'_const_smul A (by norm_num), Real.enorm_eq_ofReal hA]
    _ ≤ _ := by
      apply mul_le_mul' le_rfl
      have hbound := pullback_lintegral_le volume hS
        (fun x _ => (hφ.differentiable (by simp)).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
        hinj J hJ (fun x => ‖g x‖ₑ ^ (2 : ℝ))
      simpa only [eLpNorm'_eq_lintegral_enorm, Function.comp_apply,
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (1 / 2 : ℝ))] using
        ENNReal.rpow_le_rpow hbound (by norm_num : 0 ≤ (1 / 2 : ℝ))

lemma cutoffPullback_derivative_L2 (η : E → ℂ) (hηc : HasCompactSupport η)
    (hη : ContDiff ℝ ∞ η) (φ : E → E) (hφ : ContDiff ℝ ∞ φ)
    (hinj : Set.InjOn φ (tsupport η)) (J : ℝ≥0)
    (hJ : ∀ x ∈ tsupport η, 1 ≤ (J : ℝ≥0∞) * ENNReal.ofReal |(fderiv ℝ φ x).det|)
    (N : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (s : ℝ), (N : ℝ) ≤ s → ∀ f : 𝓢(E, ℂ),
      ∀ n ≤ N, eLpNorm (iteratedFDeriv ℝ n (cutoffPullback η hηc hη φ hφ f)) 2 volume ≤
        ENNReal.ofReal (C * ‖schwartzToSobolev s f‖) := by
  obtain ⟨A, hA, ha⟩ := cutoff_comp_derivative_bound hηc hη hφ N
  obtain ⟨B, hB, hb⟩ := jetMajorant_eLpNorm_bound (E := E) N
  let D : ℝ := (J : ℝ) ^ (1 / 2 : ℝ)
  have hD : 0 ≤ D := Real.rpow_nonneg J.coe_nonneg _
  have heD : (J : ℝ≥0∞) ^ (1 / 2 : ℝ) = ENNReal.ofReal D := by
    dsimp only [D]
    simpa only [ENNReal.ofReal_coe_nnreal] using
      (ENNReal.ofReal_rpow_of_nonneg (p := (1 / 2 : ℝ)) J.coe_nonneg (by norm_num))
  refine ⟨A * (D + 1) * B, by positivity, fun s hs f n hn => ?_⟩
  let g := cutoffPullback η hηc hη φ hφ f
  have hsup : Function.support (iteratedFDeriv ℝ n g) ⊆ tsupport η :=
    (support_iteratedFDeriv_subset n).trans tsupport_mul_subset_left
  have hbound : eLpNorm (iteratedFDeriv ℝ n g) 2 volume ≤
      ENNReal.ofReal A * ((J : ℝ≥0∞) ^ (1 / 2 : ℝ) * eLpNorm (jetMajorant N f) 2 volume) := by
    have hmeas : AEStronglyMeasurable (iteratedFDeriv ℝ n g) (volume : Measure E) :=
      ((g.smooth ⊤).continuous_iteratedFDeriv
        (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).aestronglyMeasurable
    rw [eLpNorm_eq_eLpNorm' (p := 2) (by norm_num) (by norm_num),
      eLpNorm_eq_eLpNorm' (p := 2) (by norm_num) (by norm_num)]
    norm_num only [ENNReal.toReal_ofNat]
    exact supported_pullback_eLpNorm_le isClosed_closure.measurableSet hsup hφ hinj
      J hJ (jetMajorant N f) A hA.le (ha f (f.smooth ⊤) n hn)
  apply hbound.trans
  calc
    ENNReal.ofReal A * ((J : ℝ≥0∞) ^ (1 / 2 : ℝ) * eLpNorm (jetMajorant N f) 2 volume)
    _ ≤ ENNReal.ofReal A * (ENNReal.ofReal D *
        ENNReal.ofReal (B * ‖schwartzToSobolev s f‖)) := by
      rw [heD]
      exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (hb s hs f))
    _ = ENNReal.ofReal (A * D * B * ‖schwartzToSobolev s f‖) := by
      rw [← ENNReal.ofReal_mul hD, ← ENNReal.ofReal_mul hA.le]
      congr 1
      ring
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      gcongr
      linarith


end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_CutoffPullbackSobolevBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory
open MeasureTheory Set
open scoped ENNReal NNReal
open Function
namespace YauCounterexamples
open scoped LineDeriv
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem cutoffPullback_sobolev_bound (η : E → ℂ) (hηc : HasCompactSupport η)
    (hη : ContDiff ℝ ∞ η) (φ : E → E) (hφ : ContDiff ℝ ∞ φ)
    (hinj : Set.InjOn φ (tsupport η)) (J : ℝ≥0)
    (hJ : ∀ x ∈ tsupport η, 1 ≤ (J : ℝ≥0∞) * ENNReal.ofReal |(fderiv ℝ φ x).det|)
    (k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ f : 𝓢(E, ℂ),
      ‖schwartzToSobolev (2 * (k : ℝ)) (cutoffPullback η hηc hη φ hφ f)‖ ≤
        C * ‖schwartzToSobolev (2 * (k : ℝ)) f‖ := by
  obtain ⟨C, hC, hc⟩ := cutoffPullback_derivative_L2 η hηc hη φ hφ hinj J hJ (2 * k)
  let A : ℝ := (1 + ((2 * Real.pi) ^ 2 : ℝ)⁻¹ * Module.finrank ℝ E) ^ k
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨A * C, mul_pos hA hC, fun f => ?_⟩
  have hb : SchwartzWordBound (2 * k) (cutoffPullback η hηc hη φ hφ f)
      (C * ‖schwartzToSobolev (2 * (k : ℝ)) f‖) := by
    intro j hj w
    let g := cutoffPullback η hηc hη φ hφ f
    have hh : eLpNorm ((∂^{fun a => stdOrthonormalBasis ℝ E (w a)} g : 𝓢(E, ℂ)) : E → ℂ)
        2 volume ≤ ENNReal.ofReal (C * ‖schwartzToSobolev (2 * (k : ℝ)) f‖) := by
      refine (eLpNorm_mono_real (g := fun x => ‖iteratedFDeriv ℝ j g x‖)
        ?_).trans ?_
      · intro x
        rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
        simpa only [OrthonormalBasis.norm_eq_one, Finset.prod_const_one, mul_one] using
          (iteratedFDeriv ℝ j g x).le_opNorm (fun a => stdOrthonormalBasis ℝ E (w a))
      · rw [eLpNorm_norm (iteratedFDeriv ℝ j g)]
        exact hc (2 * (k : ℝ)) (by norm_num) f j hj
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
    simpa only [g, SchwartzMap.norm_toLp, ENNReal.toReal_ofReal (mul_nonneg hC.le (norm_nonneg _))] using h
  simpa only [A, mul_assoc] using sobolev_even_le_word_bound k
    (cutoffPullback η hηc hη φ hφ f) (C * ‖schwartzToSobolev (2 * (k : ℝ)) f‖) hb

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_FlowInitialFderiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory intervalIntegral
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal

theorem smooth_extension_near_compact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K O : Set E} (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    {φ : E → F} (hφ : ContDiffOn ℝ ∞ φ O) :
    ∃ ψ : E → F, ContDiff ℝ ∞ ψ ∧ φ =ᶠ[𝓝ˢ K] ψ := by
  obtain ⟨V, hV, hKV, hVO⟩ := normal_exists_closure_subset hK.isClosed hO hKO
  obtain ⟨η, hηone, hηzero, _⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (I := 𝓘(ℝ, E)) (n := ⊤) (t := V)
      hK.isClosed (by simpa only [hV.interior_eq] using hKV)
  have hη : ContDiff ℝ ∞ η := contMDiff_iff_contDiff.mp η.contMDiff
  have hsη : tsupport η ⊆ O := by
    apply (closure_mono (show support η ⊆ V from ?_)).trans hVO
    intro x hx
    by_contra hn
    exact hx (hηzero x hn)
  refine ⟨fun x => η x • φ x, ?_, ?_⟩
  · rw [← contMDiff_iff_contDiff]
    apply contMDiff_of_tsupport
    intro x hx
    have hxO : x ∈ O := hsη (tsupport_smul_subset_left η φ hx)
    rw [contMDiffAt_iff_contDiffAt]
    exact hη.contDiffAt.smul ((hφ x hxO).contDiffAt (hO.mem_nhds hxO))
  · filter_upwards [hηone] with x hx
    simp only [hx, one_smul]


end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory intervalIntegral
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
open Set Filter Function Metric
open scoped Topology ContDiff
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Function Metric
open scoped Topology ContDiff NNReal



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_LocalIntegrationParts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

def metricFirstCoefficient (g : SmoothMetric E M) (p : M) (j : CoordIndex E) (y : E) : ℝ :=
  (Real.sqrt (metricCoefficients g p y).det)⁻¹ * ∑ i,
    fderiv ℝ (fun z => Real.sqrt (metricCoefficients g p z).det *
      (metricCoefficients g p z)⁻¹ i j) y (Module.finBasis ℝ E i)

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ConstantComplexProductJetBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory
open MeasureTheory Set
open scoped ENNReal NNReal
open Function
open Set Function Filter
open scoped Topology Manifold ContDiff SchwartzMap
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

def chartLocalize (p : M) (η u : M → ℂ) (y : E) : ℂ := by
  classical
  exact if y ∈ (chartAt E p).target then η ((chartAt E p).symm y) * u ((chartAt E p).symm y) else 0

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedSpace ℝ E] [T2Space M] in
lemma chartLocalize_eq (p : M) (η u : M → ℂ) {y : E} (hy : y ∈ (chartAt E p).target) :
    chartLocalize (E := E) p η u y = η ((chartAt E p).symm y) * u ((chartAt E p).symm y) := ite_eq_left hy

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedSpace ℝ E] [T2Space M] in
lemma support_chartLocalize (p : M) (η u : M → ℂ) :
    support (chartLocalize (E := E) p η u) ⊆ (chartAt E p) '' tsupport η := by
  intro y hy
  by_cases hy' : y ∈ (chartAt E p).target
  · refine ⟨(chartAt E p).symm y, ?_, (chartAt E p).right_inv hy'⟩
    apply subset_tsupport
    intro hzero
    apply hy
    simp only [chartLocalize, ite_eq_left hy', hzero, zero_mul]
  · exact False.elim (hy (by simp only [chartLocalize, ite_eq_right hy']))

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedSpace ℝ E] [T2Space M] in
lemma isCompact_chartSupport (p : M) (η : M → ℂ)
    (hη : HasCompactSupport η) (hs : tsupport η ⊆ (chartAt E p).source) :
    IsCompact ((chartAt E p) '' tsupport η) :=
  hη.image_of_continuousOn ((chartAt E p).continuousOn.mono hs)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedSpace ℝ E] [T2Space M] in
lemma hasCompactSupport_chartLocalize (p : M) (η u : M → ℂ)
    (hη : HasCompactSupport η) (hs : tsupport η ⊆ (chartAt E p).source) :
    HasCompactSupport (chartLocalize (E := E) p η u) :=
  (isCompact_chartSupport (E := E) p η hη hs).of_isClosed_subset isClosed_closure
    (closure_minimal (support_chartLocalize (E := E) p η u) (isCompact_chartSupport (E := E) p η hη hs).isClosed)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedSpace ℝ E] [T2Space M] in
lemma tsupport_chartLocalize_subset (p : M) (η u : M → ℂ)
    (hη : HasCompactSupport η) (hs : tsupport η ⊆ (chartAt E p).source) :
    tsupport (chartLocalize (E := E) p η u) ⊆ (chartAt E p).target := by
  exact (closure_minimal (support_chartLocalize (E := E) p η u)
    (isCompact_chartSupport (E := E) p η hη hs).isClosed).trans
    (image_subset_iff.mpr fun x hx => (chartAt E p).map_source (hs hx))

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma contDiff_chartLocalize (p : M) (η u : M → ℂ)
    (hηc : HasCompactSupport η) (hs : tsupport η ⊆ (chartAt E p).source)
    (hη : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ η)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ u) :
    ContDiff ℝ ∞ (chartLocalize (E := E) p η u) := by
  rw [← contMDiff_iff_contDiff]
  apply contMDiff_of_tsupport
  intro y hy
  have hyt := tsupport_chartLocalize_subset (E := E) p η u hηc hs hy
  have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (chartAt E p).symm y :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hyt
  rw [contMDiffAt_iff_contDiffAt]
  have ha : ContDiffAt ℝ ∞ (η ∘ (chartAt E p).symm) y :=
    contMDiffAt_iff_contDiffAt.mp (hη.contMDiffAt.comp y hc)
  have hb : ContDiffAt ℝ ∞ (u ∘ (chartAt E p).symm) y :=
    contMDiffAt_iff_contDiffAt.mp (hu.contMDiffAt.comp y hc)
  apply (ha.mul hb).congr_of_eventuallyEq
  filter_upwards [(chartAt E p).open_target.mem_nhds hyt] with z hz
  exact chartLocalize_eq (E := E) p η u hz

def chartSchwartz (p : M) (η u : M → ℂ)
    (hηc : HasCompactSupport η) (hs : tsupport η ⊆ (chartAt E p).source)
    (hη : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ η)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ u) : 𝓢(E, ℂ) :=
  (hasCompactSupport_chartLocalize (E := E) p η u hηc hs).toSchwartzMap
    (contDiff_chartLocalize (E := E) p η u hηc hs hη hu)

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma chartSchwartz_apply (p : M) (η u : M → ℂ)
    (hηc : HasCompactSupport η) (hs : tsupport η ⊆ (chartAt E p).source)
    (hη : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ η)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ u) (x : M)
    (hx : x ∈ (chartAt E p).source) :
    chartSchwartz (E := E) p η u hηc hs hη hu (chartAt E p x) = η x * u x := by
  change chartLocalize (E := E) p η u _ = _
  rw [chartLocalize_eq (E := E) p η u ((chartAt E p).map_source hx), (chartAt E p).left_inv hx]


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory
open MeasureTheory Set
open scoped ENNReal NNReal
open Function
open Set Function Filter
open scoped Topology Manifold ContDiff SchwartzMap
open Set Function Filter
open scoped Topology Manifold ContDiff SchwartzMap
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M]

abbrev ManifoldSmoothFunctions (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] :=
  C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, ℂ), ℂ⟯

def smoothToBounded : ManifoldSmoothFunctions E M →ₗ[ℝ] M →ᵇ ℂ where
  toFun u := BoundedContinuousFunction.mkOfCompact ⟨u, u.contMDiff.continuous⟩
  map_add' u v := by ext x; rfl
  map_smul' c u := by ext x; rfl

def chartSchwartzLinear (p : M) (η : M → ℂ)
    (hηc : HasCompactSupport η) (hs : tsupport η ⊆ (chartAt E p).source)
    (hη : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ η) :
    ManifoldSmoothFunctions E M →ₗ[ℝ] 𝓢(E, ℂ) where
  toFun u := chartSchwartz p η u hηc hs hη u.contMDiff
  map_add' u v := by
    ext y
    change chartLocalize (E := E) p η (u + v) y =
      chartLocalize (E := E) p η u y + chartLocalize (E := E) p η v y
    simp only [chartLocalize, Pi.add_apply]
    split_ifs <;> simp [mul_add]
  map_smul' c u := by
    ext y
    change chartLocalize (E := E) p η (c • u) y = c • chartLocalize (E := E) p η u y
    simp only [chartLocalize, Pi.smul_apply]
    split_ifs <;> simp [mul_left_comm]

variable {ι : Type*} [Fintype ι]
variable (p : ι → M) (η : ι → M → ℂ)
    (hηc : ∀ i, HasCompactSupport (η i))
    (hηs : ∀ i, tsupport (η i) ⊆ (chartAt E (p i)).source)
    (hηm : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (η i))

def atlasSobolevLocalization (s : ℝ) : ManifoldSmoothFunctions E M →ₗ[ℝ]
    (ι → FourierSobolevSpace E ℂ s) :=
  LinearMap.pi fun i =>
    ((schwartzToSobolev s).restrictScalars ℝ).toLinearMap.comp
      (chartSchwartzLinear (p i) (η i) (hηc i) (hηs i) (hηm i))

def manifoldSobolevSubmodule (s : ℝ) : Submodule ℝ (ι → FourierSobolevSpace E ℂ s) :=
  (atlasSobolevLocalization p η hηc hηs hηm s).range.topologicalClosure

abbrev ManifoldSobolev (s : ℝ) := manifoldSobolevSubmodule p η hηc hηs hηm s

instance manifoldSobolev_completeSpace (s : ℝ) :
    CompleteSpace (ManifoldSobolev p η hηc hηs hηm s) :=
  (atlasSobolevLocalization p η hηc hηs hηm s).range.isClosed_topologicalClosure.completeSpace_coe

def smoothToManifoldSobolev (s : ℝ) : ManifoldSmoothFunctions E M →ₗ[ℝ]
    ManifoldSobolev p η hηc hηs hηm s :=
  (atlasSobolevLocalization p η hηc hηs hηm s).codRestrict _ fun u =>
    Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ u)

omit [CompactSpace M] [Fintype ι] in
lemma denseRange_smoothToManifoldSobolev (s : ℝ) :
    DenseRange (smoothToManifoldSobolev p η hηc hηs hηm s) := by
  rw [DenseRange, Subtype.dense_iff]
  change closure ((atlasSobolevLocalization p η hηc hηs hηm s).range : Set (ι → FourierSobolevSpace E ℂ s)) ⊆ _
  apply closure_mono
  rintro y ⟨u, rfl⟩
  exact ⟨smoothToManifoldSobolev p η hηc hηs hηm s u, ⟨u, rfl⟩, rfl⟩


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory
open MeasureTheory Set
open scoped ENNReal NNReal
open Function
open Set Function Filter
open scoped Topology Manifold ContDiff SchwartzMap
open Set Function Filter
open scoped Topology Manifold ContDiff SchwartzMap
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M]
  {ι : Type*} [Fintype ι]
variable (p : ι → M) (η : ι → M → ℂ)
    (hηc : ∀ i, HasCompactSupport (η i))
    (hηs : ∀ i, tsupport (η i) ⊆ (chartAt E (p i)).source)
    (hηm : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (η i))

def manifoldSobolevRepresentative (s : ℝ) :
    ManifoldSobolev p η hηc hηs hηm s →L[ℝ] M →ᵇ ℂ :=
  smoothToBounded.extendOfNorm (smoothToManifoldSobolev p η hηc hηs hηm s)


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory
open MeasureTheory Set
open scoped ENNReal NNReal
open Function
open Set Function Filter
open scoped Topology Manifold ContDiff SchwartzMap
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

def chartLift (p : M) (χ : M → ℂ) (f : E → ℂ) (x : M) : ℂ := χ x * f (chartAt E p x)

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma contMDiff_chartLift (p : M) (χ : M → ℂ)
    (hχs : tsupport χ ⊆ (chartAt E p).source)
    (hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ χ) {f : E → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (chartLift (E := E) p χ f) := by
  apply contMDiff_of_tsupport
  intro x hx
  have hxs : x ∈ (chartAt E p).source := hχs (tsupport_mul_subset_left hx)
  exact ((ContinuousLinearMap.mul ℝ ℂ).contMDiff.contMDiffAt.comp x hχ.contMDiffAt).clm_apply
    ((contMDiff_iff_contDiff.mpr hf).contMDiffAt.comp x
      (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hxs))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in

lemma tsupport_chartLocalize_image (p : M) (η u : M → ℂ)
    (hηc : HasCompactSupport η) (hs : tsupport η ⊆ (chartAt E p).source) :
    tsupport (chartLocalize (E := E) p η u) ⊆ (chartAt E p) '' tsupport η :=
  closure_minimal (support_chartLocalize p η u)
    (isCompact_chartSupport p η hηc hs).isClosed

omit [FiniteDimensional ℝ E] [T2Space M] in

lemma contDiffOn_chartTransition (p q : M) :
    ContDiffOn ℝ ∞ ((chartAt E p).symm.trans (chartAt E q))
      ((chartAt E p).symm.trans (chartAt E q)).source := by
  intro y hy
  have hy' : y ∈ (chartAt E p).target ∧ (chartAt E p).symm y ∈ (chartAt E q).source := hy
  exact (contMDiffAt_iff_contDiffAt.mp
    ((contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q) hy'.2).comp y
      (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hy'.1))).contDiffWithinAt

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
lemma chart_overlap_cutoff_support (p q : M) (η χ : M → ℂ)
    (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ (chartAt E p).source)
    (hχs : tsupport χ ⊆ (chartAt E q).source) :
    tsupport (chartLocalize (E := E) p (η * χ) (fun _ => 1)) ⊆
      ((chartAt E p).symm.trans (chartAt E q)).source := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := tsupport_chartLocalize_image p (η * χ) (fun _ => 1)
    (hηc.mul_right (f' := χ)) (tsupport_mul_subset_left.trans hηs) hy
  have hxp := hηs (tsupport_mul_subset_left hx)
  refine ⟨(chartAt E p).map_source hxp, ?_⟩
  change (chartAt E p).symm (chartAt E p x) ∈ (chartAt E q).source
  rw [(chartAt E p).left_inv hxp]
  exact hχs (tsupport_mul_subset_right hx)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
lemma chartLocalize_chartLift (p q : M) (η χ : M → ℂ) (f : E → ℂ) (y : E) :
    chartLocalize (E := E) p η (chartLift (E := E) q χ f) y =
      chartLocalize (E := E) p (η * χ) (fun _ => 1) y *
        f (((chartAt E p).symm.trans (chartAt E q)) y) := by
  classical
  by_cases hy : y ∈ (chartAt E p).target
  · simp only [chartLocalize_eq p _ _ hy, chartLift, Pi.mul_apply, mul_one,
      OpenPartialHomeomorph.trans_apply, mul_assoc]
  · simp only [chartLocalize, ite_eq_right hy, zero_mul]


open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ContMDiffComplexMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory
open MeasureTheory Set
open scoped ENNReal NNReal
open Function
open Set Function Filter
open scoped Topology Manifold ContDiff SchwartzMap
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
open scoped SchwartzMap ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
lemma contMDiff_complex_mul {η χ : M → ℂ}
    (hη : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ η)
    (hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ χ) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (η * χ) :=
  ((ContinuousLinearMap.mul ℝ ℂ).contMDiff.comp hη).clm_apply hχ



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_LocalMetricInverse
attribute [-instance] _root_.OAI.YauCounterexamples.manifoldSobolev_completeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
namespace YauCounterexamples
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

structure LocalMetricInverse (g : SmoothMetric E M) (p : M) (s : ℝ)
    (hs : Module.finrank ℝ E < 2 * s) where
  radius : ℝ
  radius_pos : 0 < radius
  bound : ℝ
  bound_pos : 0 < bound
  in_target : Metric.closedBall ((chartAt E p) p) radius ⊆ (chartAt E p).target
  inverse : (α : ℝ) → 1 ≤ α →
    FourierSobolevSpace E ℂ s →L[ℂ] FourierSobolevSpace E ℂ (s + 2)
  norm_bound : ∀ (α : ℝ) (hα : 1 ≤ α), ‖inverse α hα‖ ≤ bound
  half_bound : ∀ (α : ℝ) (hα : 1 ≤ α) f,
    ‖sobolevInclusion (s + 2) (s + 1) (by linarith) (inverse α hα f)‖ ≤
      bound * (Real.sqrt α)⁻¹ * ‖f‖
  equation : ∀ (α : ℝ) (hα : 1 ≤ α) (ht : Module.finrank ℝ E < 2 * (s + 2)) f x, ‖x‖ ≤ 1 →
    (α : ℂ) * sobolevRepresentative ht (inverse α hα f) x -
      (∑ i, ∑ j, ((metricCoefficients g p ((chartAt E p) p + radius • x))⁻¹ i j : ℂ) *
        fderiv ℝ (fun y => fderiv ℝ (sobolevRepresentative ht (inverse α hα f) : E → ℂ)
          y (Module.finBasis ℝ E j)) x (Module.finBasis ℝ E i)) -
      (radius : ℂ) * ∑ i, (metricFirstCoefficient g p i ((chartAt E p) p + radius • x) : ℂ) *
        fderiv ℝ (sobolevRepresentative ht (inverse α hα f) : E → ℂ) x (Module.finBasis ℝ E i) =
      sobolevRepresentative hs f x

def metricInversePatch {g : SmoothMetric E M} {p : M} {s : ℝ}
    {hs : Module.finrank ℝ E < 2 * s} (D : LocalMetricInverse g p s hs) : Set M :=
  (chartAt E p).source ∩ (chartAt E p) ⁻¹' Metric.ball ((chartAt E p) p) (D.radius / 2)

end YauCounterexamples


end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_BoundedDegreeMonomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff

section CoefficientContinuity
open MvPolynomial
variable {σ X : Type*} [TopologicalSpace X]

def CoeffContinuous (F : X → MvPolynomial σ ℂ) : Prop :=
  ∀ m : σ →₀ ℕ, Continuous (fun x => (F x).coeff m)

end CoefficientContinuity

open MvPolynomial



end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_RealForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
namespace YauCounterexamples
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

abbrev RealForm (V : Type*) [AddCommGroup V] [Module ℝ V] :=
  LinearMap.BilinForm ℝ V

def innerForm : RealForm V :=
  LinearMap.mk₂ ℝ (inner ℝ)
    (fun _ _ _ => inner_add_left _ _ _)
    (fun _ _ _ => real_inner_smul_left _ _ _)
    (fun _ _ _ => inner_add_right _ _ _)
    (fun _ _ _ => real_inner_smul_right _ _ _)

@[simp] theorem innerForm_apply (x y : V) : innerForm x y = inner ℝ x y := rfl

def StrictlyBelow (U H : RealForm V) : Prop :=
  ∀ x : V, x ≠ 0 → U x x < H x x

structure AdmissiblePhaseHessian (H : RealForm V) (a b : V) where
  realPart : RealForm V
  imagPart : RealForm V
  real_symm : realPart.IsSymm
  imag_symm : imagPart.IsSymm
  column_b : ∀ x, imagPart b x = realPart a x
  column_a : ∀ x, imagPart a x = -realPart b x
  gap : StrictlyBelow realPart H

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartDerivativeNeZeroTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory
open MeasureTheory Set
open scoped ENNReal NNReal
open Function
open Set Function Filter
open scoped Topology Manifold ContDiff SchwartzMap
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
open scoped SchwartzMap ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] {ι : Type*} [Fintype ι]
variable (p : ι → M) (η : ι → M → ℂ)
    (hηc : ∀ i, HasCompactSupport (η i))
    (hηs : ∀ i, tsupport (η i) ⊆ (chartAt E (p i)).source)
    (hηm : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (η i))
variable (q : M) (χ : M → ℂ) (hχs : tsupport χ ⊆ (chartAt E q).source)
    (hχm : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ χ)

def chartLiftSmoothLinear : 𝓢(E, ℂ) →ₗ[ℝ] ManifoldSmoothFunctions E M where
  toFun f := ⟨chartLift q χ f, contMDiff_chartLift q χ hχs hχm (f.smooth ⊤)⟩
  map_add' f g := by
    ext x
    change χ x * (f (chartAt E q x) + g (chartAt E q x)) =
      χ x * f (chartAt E q x) + χ x * g (chartAt E q x)
    exact mul_add _ _ _
  map_smul' c f := by
    ext x
    change χ x * ((c : ℂ) * f (chartAt E q x)) = (c : ℂ) * (χ x * f (chartAt E q x))
    ring

def chartLiftToManifoldSobolev (s : ℝ) : 𝓢(E, ℂ) →ₗ[ℝ]
    ManifoldSobolev p η hηc hηs hηm s :=
  (smoothToManifoldSobolev p η hηc hηs hηm s).comp (chartLiftSmoothLinear q χ hχs hχm)

def sobolevChartLift (k : ℕ) : FourierSobolevSpace E ℂ (2 * (k : ℝ)) →L[ℝ]
    ManifoldSobolev p η hηc hηs hηm (2 * (k : ℝ)) :=
  (chartLiftToManifoldSobolev p η hηc hηs hηm q χ hχs hχm (2 * (k : ℝ))).extendOfNorm
    ((schwartzToSobolev (2 * (k : ℝ))).restrictScalars ℝ).toLinearMap


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory
open MeasureTheory Set
open scoped ENNReal NNReal
open Function
open Set Function Filter
open scoped Topology Manifold ContDiff SchwartzMap
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
open scoped SchwartzMap ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {ι : Type*} [Fintype ι]
variable (p : ι → M) (η : ι → M → ℂ)
    (hηc : ∀ i, HasCompactSupport (η i))
    (hηs : ∀ i, tsupport (η i) ⊆ (chartAt E (p i)).source)
    (hηm : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (η i))
    (χ : ι → M → ℂ) (hχs : ∀ i, tsupport (χ i) ⊆ (chartAt E (p i)).source)
    (hχm : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (χ i))

include hηs hχs in
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsManifold 𝓘(ℝ, E) ∞ M] [Fintype ι] in
lemma chartLift_chartLocalize_buffer (i : ι) (hχone : EqOn (χ i) 1 (tsupport (η i)))
    (f : M → ℂ) (x : M) :
    chartLift (E := E) (p i) (χ i) (chartLocalize (E := E) (p i) (η i) f) x = η i x * f x := by
  change χ i x * chartLocalize (E := E) (p i) (η i) f (chartAt E (p i) x) = _
  by_cases hx : x ∈ (chartAt E (p i)).source
  · rw [chartLocalize_eq _ _ _ ((chartAt E (p i)).map_source hx), (chartAt E (p i)).left_inv hx]
    by_cases hηx : η i x = 0
    · simp [hηx]
    · rw [hχone (subset_tsupport _ hηx)]
      simp
  · have ha : η i x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hηs i h))
    have hb : χ i x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hχs i h))
    simp [ha, hb]

include hηs hχs in
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsManifold 𝓘(ℝ, E) ∞ M] in
lemma atlasGluing_partition_identity (hηone : ∀ x, ∑ i, η i x = 1)
    (hχone : ∀ i, EqOn (χ i) 1 (tsupport (η i))) (f : M → ℂ) (x : M) :
    ∑ i, chartLift (E := E) (p i) (χ i) (chartLocalize (E := E) (p i) (η i) f) x = f x := by
  simp only [chartLift_chartLocalize_buffer p η hηs χ hχs _ (hχone _) f x]
  rw [← Finset.sum_mul, hηone x, one_mul]


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

structure CompactMetricAtlas (g : SmoothMetric E M) (k : ℕ)
    (hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))) where
  t : Finset M
  localInverse : ∀ i : t, LocalMetricInverse g (i : M) (2 * (k : ℝ)) hs
  η : t → M → ℂ
  χ : t → M → ℂ
  ψ : t → M → ℂ
  smooth_η : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (η i)
  sum_η : ∀ x, ∑ i, η i x = 1
  support_η : ∀ i, tsupport (η i) ⊆ metricInversePatch (localInverse i)
  smooth_χ : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (χ i)
  support_χ : ∀ i, tsupport (χ i) ⊆ metricInversePatch (localInverse i)
  one_χ : ∀ i, χ i =ᶠ[𝓝ˢ (tsupport (η i))] 1
  smooth_ψ : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (ψ i)
  support_ψ : ∀ i, tsupport (ψ i) ⊆ metricInversePatch (localInverse i)
  one_ψ : ∀ i, ψ i =ᶠ[𝓝ˢ (tsupport (χ i))] 1

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

abbrev p (i : A.t) : M := i
omit [T2Space M] [CompactSpace M] in
lemma chart_η (i : A.t) : tsupport (A.η i) ⊆ (chartAt E (A.p i)).source :=
  fun _ h => (A.support_η i h).1
omit [T2Space M] [CompactSpace M] in
lemma chart_χ (i : A.t) : tsupport (A.χ i) ⊆ (chartAt E (A.p i)).source :=
  fun _ h => (A.support_χ i h).1
omit [T2Space M] [CompactSpace M] in
lemma chart_ψ (i : A.t) : tsupport (A.ψ i) ⊆ (chartAt E (A.p i)).source :=
  fun _ h => (A.support_ψ i h).1

abbrev H (s : ℝ) := ManifoldSobolev A.p A.η
  (fun i => HasCompactSupport.of_compactSpace (A.η i)) A.chart_η A.smooth_η s

def representative (s : ℝ) : A.H s →L[ℝ] M →ᵇ ℂ :=
  manifoldSobolevRepresentative A.p A.η
    (fun i => HasCompactSupport.of_compactSpace (A.η i)) A.chart_η A.smooth_η s

def lift (q : M) (ξ : M → ℂ) (hξs : tsupport ξ ⊆ (chartAt E q).source)
    (hξ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ ξ) (l : ℕ) :
    FourierSobolevSpace E ℂ (2 * (l : ℝ)) →L[ℝ] A.H (2 * (l : ℝ)) :=
  sobolevChartLift A.p A.η (fun i => HasCompactSupport.of_compactSpace (A.η i))
    A.chart_η A.smooth_η q ξ hξs hξ l

def χcoord (i : A.t) : E → ℂ := chartLocalize (E := E) (A.p i) (A.χ i) 1
omit [T2Space M] in
lemma compact_χcoord (i : A.t) : HasCompactSupport (A.χcoord i) :=
  hasCompactSupport_chartLocalize (A.p i) (A.χ i) 1
    (HasCompactSupport.of_compactSpace _) (A.chart_χ i)
omit [T2Space M] in
lemma smooth_χcoord (i : A.t) : ContDiff ℝ ∞ (A.χcoord i) :=
  contDiff_chartLocalize (A.p i) (A.χ i) 1
    (HasCompactSupport.of_compactSpace _) (A.chart_χ i) (A.smooth_χ i) contMDiff_const

def localize (s : ℝ) (i : A.t) : A.H s →L[ℝ] FourierSobolevSpace E ℂ s :=
  (ContinuousLinearMap.proj i) ∘L
    (manifoldSobolevSubmodule A.p A.η (fun j => HasCompactSupport.of_compactSpace (A.η j))
      A.chart_η A.smooth_η s).subtypeL

end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

def ψcoord (i : A.t) : E → ℂ := chartLocalize (E := E) (A.p i) (A.ψ i) 1
omit [T2Space M] in
lemma compact_ψcoord (i : A.t) : HasCompactSupport (A.ψcoord i) :=
  hasCompactSupport_chartLocalize (A.p i) (A.ψ i) 1
    (HasCompactSupport.of_compactSpace _) (A.chart_ψ i)
omit [T2Space M] in
lemma smooth_ψcoord (i : A.t) : ContDiff ℝ ∞ (A.ψcoord i) :=
  contDiff_chartLocalize (A.p i) (A.ψ i) 1
    (HasCompactSupport.of_compactSpace _) (A.chart_ψ i) (A.smooth_ψ i) contMDiff_const

structure PatchCoefficients (i : A.t) where
  a : CoordIndex E → CoordIndex E → E → ℝ
  c : CoordIndex E → E → ℝ
  smooth_a : ∀ j l, ContDiff ℝ ∞ (a j l)
  smooth_c : ∀ j, ContDiff ℝ ∞ (c j)
  eq_a : ∀ x ∈ tsupport (A.χcoord i), ∀ j l, a j l x = (metricCoefficients g (A.p i) x)⁻¹ j l
  eq_c : ∀ x ∈ tsupport (A.χcoord i), ∀ j, c j x = metricFirstCoefficient g (A.p i) j x

end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

def ofSmooth (s : ℝ) (f : ManifoldSmoothFunctions E M) : A.H s :=
  smoothToManifoldSobolev A.p A.η (fun i => HasCompactSupport.of_compactSpace (A.η i))
    A.chart_η A.smooth_η s f

end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction SchwartzMap
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
lemma smooth_partition (f : ManifoldSmoothFunctions E M) :
    ∑ i, chartLiftSmoothLinear (A.p i) (A.χ i) (A.chart_χ i) (A.smooth_χ i)
      (chartSchwartzLinear (A.p i) (A.η i) (HasCompactSupport.of_compactSpace _)
        (A.chart_η i) (A.smooth_η i) f) = f := by
  ext x
  simp only [← ContMDiffMap.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
  exact atlasGluing_partition_identity A.p A.η A.chart_η A.χ A.chart_χ A.sum_η
    (fun i y hy => (A.one_χ i).self_of_nhdsSet hy) f x

def smoothCutoffLocalization (q : M) (ξ : M → ℂ)
    (hξs : tsupport ξ ⊆ (chartAt E q).source)
    (hξ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ ξ) (l : ℕ) :
    ManifoldSmoothFunctions E M →ₗ[ℝ] FourierSobolevSpace E ℂ (2 * (l : ℝ)) :=
  ((schwartzToSobolev (2 * (l : ℝ))).restrictScalars ℝ).toLinearMap.comp
    (chartSchwartzLinear q ξ (HasCompactSupport.of_compactSpace ξ) hξs hξ)

def cutoffLocalization (q : M) (ξ : M → ℂ)
    (hξs : tsupport ξ ⊆ (chartAt E q).source)
    (hξ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ ξ) (l : ℕ) :
    A.H (2 * (l : ℝ)) →L[ℝ] FourierSobolevSpace E ℂ (2 * (l : ℝ)) :=
  (smoothCutoffLocalization q ξ hξs hξ l).extendOfNorm
    (smoothToManifoldSobolev A.p A.η (fun i => HasCompactSupport.of_compactSpace (A.η i))
      A.chart_η A.smooth_η (2 * (l : ℝ)))

local instance H_smulCommClass (s : ℝ) : SMulCommClass ℝ ℝ (A.H s) where
  smul_comm r t x := by rw [smul_smul, smul_smul, mul_comm]

local instance H_isScalarTower (s : ℝ) : IsScalarTower ℝ ℝ (A.H s) where
  smul_assoc r t x := mul_smul r t x

end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open scoped Manifold BoundedContinuousFunction ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

def ChartJetBound (N : ℕ) (f : M → ℂ) (C : ℝ) : Prop :=
  ∀ (i : A.t) (j : ℕ), j ≤ N → ∀ y : E,
    ‖iteratedFDeriv ℝ j (chartLocalize (E := E) (A.p i) (A.η i) f) y‖ ≤ C

end CompactMetricAtlas

end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs)

abbrev highIndex (_A : CompactMetricAtlas g k hs) : ℝ := 2*((k+1:ℕ):ℝ)
end CompactMetricAtlas

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_VaryingPatchCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Function
open scoped Topology
namespace YauCounterexamples
open Set Filter Function
open scoped ContDiff Topology Manifold BoundedContinuousFunction SchwartzMap
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

structure VaryingPatchCoefficients (q : SmoothMetric E M) (i : A.t) where
  a : CoordIndex E → CoordIndex E → E → ℝ
  c : CoordIndex E → E → ℝ
  smooth_a : ∀ j l, ContDiff ℝ ∞ (a j l)
  smooth_c : ∀ j, ContDiff ℝ ∞ (c j)
  eq_a : ∀ x ∈ tsupport (A.χcoord i), ∀ j l, a j l x = (metricCoefficients q (A.p i) x)⁻¹ j l
  eq_c : ∀ x ∈ tsupport (A.χcoord i), ∀ j, c j x = metricFirstCoefficient q (A.p i) j x

end CompactMetricAtlas
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_CoefficientPerturbationTendsto
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Function
open scoped Topology
open Set Filter Function
open scoped Topology ContDiff Manifold BoundedContinuousFunction SchwartzMap
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

@[reducible] local instance H_nacg (s : ℝ) : NormedAddCommGroup (A.H s) := inferInstance
@[reducible] local instance H_ns (s : ℝ) : NormedSpace ℝ (A.H s) := inferInstance

end CompactMetricAtlas


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartGradientProjectionSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open scoped Manifold ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs)

def scalarChartSupport (i : A.t) : Set E :=
  (chartAt E (A.p i)) '' tsupport (A.η i)

omit [T2Space M] in
lemma scalarChartSupport_compact (i : A.t) : IsCompact (A.scalarChartSupport i) :=
  isCompact_chartSupport (E:=E) (A.p i) (A.η i) (HasCompactSupport.of_compactSpace _) (A.chart_η i)

omit [T2Space M] [CompactSpace M] in
lemma scalarChartSupport_target (i : A.t) :
    A.scalarChartSupport i ⊆ (chartAt E (A.p i)).target :=
  image_subset_iff.mpr (fun _x hx => (chartAt E (A.p i)).map_source (A.chart_η i hx))

end CompactMetricAtlas

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_RealValueCubic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
namespace YauCounterexamples.BoundedAlgebra
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

def power (p : A →L[ℝ] A →L[ℝ] A) (e x : A) : ℕ → A :=
  Nat.rec e (fun _ y => p x y)

def remainder (p : A →L[ℝ] A →L[ℝ] A) (e h : A) : A :=
  (10 : ℝ) • power p e h 2 + (10 : ℝ) • power p e h 3 +
    (5 : ℝ) • power p e h 4 + power p e h 5

def remainderConstant (K U : ℝ) : ℝ :=
  20 * K ^ 2 * U + 30 * K ^ 3 * U + 20 * K ^ 4 * U + 5 * K ^ 5 * U

def polynomial (p : A →L[ℝ] A →L[ℝ] A) (e c s h : A) : A :=
  (c - s) + p ((5 : ℝ) • (c - e) - (s - e)) h + p c (remainder p e h)

end YauCounterexamples.BoundedAlgebra

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
namespace YauCounterexamples.BoundedAlgebra
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def cubicPerturbation (p : X →L[ℝ] X →L[ℝ] X) (e x : X) : X :=
  e + (3 : ℝ) • x + (3 : ℝ) • power p e x 2 + power p e x 3

end YauCounterexamples.BoundedAlgebra

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CutoffFactorCompactRaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples



open Set Filter Function Manifold
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [CompactSpace M]

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
  (A : CompactMetricAtlas g k hs)

def coveringRawTest (i₀ : CoordIndex E) (i : A.t) : CoordinateTest E M where
  center := A.p i
  compactSet := A.scalarChartSupport i
  isCompact := A.scalarChartSupport_compact i
  inTarget := A.scalarChartSupport_target i
  order := 0
  row := i₀
  column := i₀

noncomputable def coveringRawTests (i₀ : CoordIndex E) : List (CoordinateTest E M) :=
  (Finset.univ : Finset A.t).toList.map (A.coveringRawTest i₀)

end CompactMetricAtlas

end YauCounterexamples
end

end OAI
end



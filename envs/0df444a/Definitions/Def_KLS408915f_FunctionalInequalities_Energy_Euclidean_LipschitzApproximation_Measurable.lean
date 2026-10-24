-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
-- name    : KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:33:45.301983+00:00
-- url     : https://prove2.me/theorems/228ac0ad-313c-444a-823a-9d8ce07603ae
-- title:
--   Measurability and approximation tools for Lipschitz energies
-- statement:
--   `tendsto_eLpNorm_zero_of_dominated` gives dominated convergence of the extended $L^p$ seminorm for $0<p<\infty$ when the functions are almost-everywhere strongly measurable, dominated by a function in `MemLp`, and converge almost everywhere to zero. `measurable_gradient` and `aestronglyMeasurable_gradient` provide measurability of the canonical Hilbert gradient under the stated Borel and separability assumptions. `ae_differentiableAt_of_locallyLipschitz` gives almost-everywhere differentiability for locally Lipschitz real functions with respect to an additive Haar measure, and `radius` supplies the positive sequence $1/(j+1)$ tending to zero.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Euclidean/LipschitzApproximation/Measurable.lean#L26-L96 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.Measurable`, definition bundle `KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff ENNReal
namespace FunctionalInequalities
namespace Energy
namespace Euclidean
namespace LipschitzApproximation
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Measurable
variable [MeasurableSpace E]
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- Dominated convergence for the `L^p` seminorm, `0 < p < ∞`. -/
theorem tendsto_eLpNorm_zero_of_dominated {V : Type*} [NormedAddCommGroup V]
    (μ : Measure E) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤)
    {F : ℕ → E → V} (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    {bound : E → ℝ} (hbound : MemLp bound p μ)
    (hle : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ bound x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) p μ) atTop (𝓝 0) := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  simp_rw [eLpNorm_eq_eLpNorm' hp0 hp, eLpNorm']
  have h : Tendsto (fun n => ∫⁻ x, ‖F n x‖ₑ ^ p.toReal ∂μ) atTop (𝓝 (∫⁻ x, (0 : ℝ≥0∞) ∂μ)) := by
    refine tendsto_lintegral_of_dominated_convergence' (fun x => ‖bound x‖ₑ ^ p.toReal)
      (fun n => ((hF n).enorm.pow_const _)) (fun n => ?_) ?_ ?_
    · filter_upwards [hle n] with x hx
      have : ‖F n x‖ₑ ≤ ‖bound x‖ₑ := by
        rw [enorm_eq_nnnorm, enorm_eq_nnnorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe,
          coe_nnnorm, coe_nnnorm]
        exact hx.trans (le_abs_self _)
      exact ENNReal.rpow_le_rpow this hq.le
    · exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp hbound.eLpNorm_lt_top).ne
    · filter_upwards [hlim] with x hx
      have h0 : Tendsto (fun n => ‖F n x‖ₑ) atTop (𝓝 0) := by
        have := (continuous_enorm.tendsto (0 : V)).comp hx
        simp only [Function.comp_def, enorm_zero] at this
        exact this
      have := (ENNReal.continuous_rpow_const (y := p.toReal)).tendsto 0 |>.comp h0
      simpa [Function.comp_def, ENNReal.zero_rpow_of_pos hq] using this
  simp only [lintegral_zero] at h
  have := (ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0 |>.comp h
  simpa [Function.comp_def, ENNReal.zero_rpow_of_pos (inv_pos.mpr hq),
    ENNReal.zero_rpow_of_pos (by positivity : 0 < 1 / p.toReal)] using this
section GradientMeasurability
variable [BorelSpace E] [CompleteSpace E]
theorem measurable_gradient (f : E → ℝ) : Measurable (gradient f) :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp (measurable_fderiv ℝ f)
variable [SecondCountableTopology E]
theorem aestronglyMeasurable_gradient (f : E → ℝ) (μ : Measure E) :
    AEStronglyMeasurable (gradient f) μ :=
  (measurable_gradient f).aestronglyMeasurable
end GradientMeasurability
variable [BorelSpace E] [FiniteDimensional ℝ E]
/-- Rademacher's theorem for locally Lipschitz real functions. -/
theorem ae_differentiableAt_of_locallyLipschitz {f : E → ℝ} (hf : LocallyLipschitz f)
    (m : Measure E) [m.IsAddHaarMeasure] : ∀ᵐ x ∂m, DifferentiableAt ℝ f x := by
  have h : ∀ n : ℕ, ∀ᵐ x ∂m, x ∈ Metric.ball (0 : E) n → DifferentiableAt ℝ f x := by
    intro n
    obtain ⟨K, hK⟩ := lipschitzOnWith_of_locallyLipschitz_of_isCompact hf (isCompact_closedBall (0 : E) n)
    obtain ⟨g, hg, hfg⟩ := hK.extend_real
    filter_upwards [hg.ae_differentiableAt (μ := m)] with x hx hxn
    have : f =ᶠ[𝓝 x] g := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hxn] with y hy
      exact hfg (Metric.ball_subset_closedBall hy)
    exact hx.congr_of_eventuallyEq this
  filter_upwards [ae_all_iff.mpr h] with x hx
  obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
  exact hx n (by simpa using hn)
/-- The radii `1 / (j + 1)` used for the approximating sequences. -/
def radius (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
theorem radius_pos (j : ℕ) : 0 < radius j := by unfold radius; positivity
theorem tendsto_radius : Tendsto radius atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
end Measurable
end LipschitzApproximation
end Euclidean
end Energy
end FunctionalInequalities



-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactPrior
-- name    : KLS408915f_FunctionalInequalities_Probability_Posterior_CompactPrior
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T04:56:28.11314+00:00
-- url     : https://prove2.me/theorems/74e8b67c-6400-433f-aaf4-4a943d0ba1f8
-- title:
--   Integrability and probability of compactly supported tilts
-- statement:
--   For a probability measure $\mu$ on a topological measurable space, `integrable_of_bound_on_support` states that a measurable real function bounded in norm on the topological support of $\mu$ is integrable. If the support is compact, `exists_bound_on_support_of_compact` supplies a nonnegative bound for every continuous real function, and `integrable_exp_mul_of_compact` and `integrable_exp_of_compact` establish integrability of $e^{\phi}f$ and $e^{\phi}$ under the stated measurability and boundedness hypotheses. Consequently, `isProbabilityMeasure_tilted_of_compact` states that the exponential tilt by any continuous exponent is a probability measure.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/CompactPrior.lean#L28-L68 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.CompactPrior`, definition bundle `KLS408915f_FunctionalInequalities_Probability_Posterior_CompactPrior`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_Exponent
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.Covariance

noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace
namespace FunctionalInequalities
namespace Probability
namespace Posterior
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [SecondCountableTopology Ω]
omit [BorelSpace Ω] in
/-- A measurable function bounded on the support is integrable. -/
theorem integrable_of_bound_on_support (μ : ProbabilityMeasure Ω) {f : Ω → ℝ}
    (hf : Measurable f) (C : ℝ)
    (hb : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C) : Integrable f (μ : Measure Ω) := by
  refine (integrable_const C).mono' hf.aestronglyMeasurable ?_
  filter_upwards [(μ : Measure Ω).support_mem_ae] with x hx
  exact hb x hx
omit [BorelSpace Ω] [SecondCountableTopology Ω] in
/-- A continuous function is bounded on a compact support. -/
theorem exists_bound_on_support_of_compact (μ : ProbabilityMeasure Ω) (hc : IsCompact (μ : Measure Ω).support)
    {φ : Ω → ℝ} (hφ : Continuous φ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ x ∈ (μ : Measure Ω).support, ‖φ x‖ ≤ P := by
  obtain ⟨P, hP⟩ := hc.exists_bound_of_continuousOn hφ.continuousOn
  exact ⟨max P 0, le_max_right _ _, fun x hx => (hP x hx).trans (le_max_left _ _)⟩
/-- `e^{φ} f` is integrable for continuous `φ` and `f` bounded on a compact support. -/
theorem integrable_exp_mul_of_compact (μ : ProbabilityMeasure Ω) (hc : IsCompact (μ : Measure Ω).support)
    {φ f : Ω → ℝ} (hφ : Continuous φ) (hf : Measurable f) {C : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C) :
    Integrable (fun x => Real.exp (φ x) * f x) (μ : Measure Ω) := by
  obtain ⟨P, _hP, hp⟩ := exists_bound_on_support_of_compact μ hc hφ
  apply integrable_of_bound_on_support μ ((Real.continuous_exp.comp hφ).measurable.mul hf) (Real.exp P * C)
  intro x hx
  change ‖Real.exp (φ x) * f x‖ ≤ Real.exp P * C
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul ?_ (hb x hx) (norm_nonneg _) (Real.exp_nonneg P)
  apply Real.exp_le_exp.mpr
  exact (le_abs_self (φ x)).trans (by simpa only [Real.norm_eq_abs] using hp x hx)
/-- `e^{φ}` is integrable for continuous `φ` on a compact support. -/
theorem integrable_exp_of_compact (μ : ProbabilityMeasure Ω) (hc : IsCompact (μ : Measure Ω).support)
    {φ : Ω → ℝ} (hφ : Continuous φ) : Integrable (fun x => Real.exp (φ x)) (μ : Measure Ω) := by
  simpa only [mul_one] using integrable_exp_mul_of_compact μ hc hφ
    (f := fun _ => (1 : ℝ)) measurable_const (C := 1) (by norm_num) (by intro x hx; simp)
/-- The tilt by a continuous exponent of a compactly supported law is a probability law. -/
theorem isProbabilityMeasure_tilted_of_compact (μ : ProbabilityMeasure Ω) (hc : IsCompact (μ : Measure Ω).support)
    {φ : Ω → ℝ} (hφ : Continuous φ) : IsProbabilityMeasure ((μ : Measure Ω).tilted φ) :=
  isProbabilityMeasure_tilted (integrable_exp_of_compact μ hc hφ)
end Posterior
end Probability
end FunctionalInequalities



-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactPrior
-- name    : KLSModular_FunctionalInequalities_Probability_Posterior_CompactPrior
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:16:19.742237+00:00
-- url     : https://prove2.me/theorems/e9642070-1d94-4ba1-98bc-8d40d5fe9489
-- title:
--   Integrability and probability of compactly supported tilts
-- statement:
--   For a probability measure $\mu$ on a topological measurable space, `integrable_of_bound_on_support` states that a measurable real function bounded in norm on the topological support of $\mu$ is integrable. If the support is compact, `exists_bound_on_support_of_compact` supplies a nonnegative bound for every continuous real function, and `integrable_exp_mul_of_compact` and `integrable_exp_of_compact` establish integrability of $e^{\phi}f$ and $e^{\phi}$ under the stated measurability and boundedness hypotheses. Consequently, `isProbabilityMeasure_tilted_of_compact` states that the exponential tilt by any continuous exponent is a probability measure.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Probability.Posterior.Exponent
--   import Mathlib.Analysis.Calculus.ParametricIntegral
--   import Mathlib.Analysis.Calculus.Deriv.Inv
--   import Mathlib.Analysis.SpecialFunctions.ExpDeriv
--   import Mathlib.Analysis.Normed.Group.Bounded
--   import Mathlib.MeasureTheory.Measure.Support
--   import Mathlib.Probability.Moments.Covariance
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   theorem integrable_of_bound_on_support (μ : ProbabilityMeasure Ω) {f : Ω → ℝ}
--       (hf : Measurable f) (C : ℝ)
--       (hb : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C) : Integrable f (μ : Measure Ω) := by
--     refine (integrable_const C).mono' hf.aestronglyMeasurable ?_
--     filter_upwards [(μ : Measure Ω).support_mem_ae] with x hx
--     exact hb x hx
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Probability/Posterior/Exponent`](https://prove2.me/theorems/36c30d18-f69a-4499-bf5e-0d0678b5706c).
--
--   Theorems in source order:
--
--   - [`hasDerivAt_weighted_integral_of_compact`](https://prove2.me/theorems/54d90089-92ce-40ab-9311-3ac0348d33d5)
--   - [`expectation_hasDerivAt_of_compact`](https://prove2.me/theorems/33fce4ba-fea7-459e-923c-b736676bd849)
--   - [`norm_integral_tilted_le_of_compact`](https://prove2.me/theorems/ae0bd956-6f80-4999-b550-1b58967f1160)
--   - [`covariance_hasDerivAt_of_compact`](https://prove2.me/theorems/9b3908cf-2697-4638-b0df-be6209e77920)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Posterior/CompactPrior.lean) · `FunctionalInequalities.Probability.Posterior.CompactPrior` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/CompactPrior.lean#L28-L68 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.CompactPrior`, definition bundle `KLSModular_FunctionalInequalities_Probability_Posterior_CompactPrior`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_Exponent
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Measure.Support
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



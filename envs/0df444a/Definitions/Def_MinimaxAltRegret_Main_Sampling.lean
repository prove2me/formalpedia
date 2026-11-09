-- Prove2me | Definitions.Def_MinimaxAltRegret_Main_Sampling
-- name    : MinimaxAltRegret_Main_Sampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:55:55.221453+00:00
-- url     : https://prove2.me/theorems/c3de7d81-c2b4-4104-8a67-bdd7d1f3b1ee
-- title:
--   Exact fresh sampling against committed adaptive losses
-- statement:
--   On a probability space (Omega,mu), let f_t be random convex losses on X and x_t random X-valued actions. A pre-sampling filtration contains every past action and revealed loss and the committed current loss. Algorithm 2 Option II is specified by its conditional density law: for every pre-sampling measurable event E and every Borel set B in R^d,
--
--   $$\mathbb P(E\cap\{x_t\in B\})=\int_E\int_{B\cap X}p_t(y)\,dy\,d\mathbb P.$$
--
--   Here p_t is computed by the corrected formula from the previous losses, and the law is required through the terminal action. This is exact fresh sampling, including against adaptive environments, with no assumed regret bound. Random actions and the hindsight regret are measurable; boundedness will supply integrability in the theorem.
--
--   **Formalization Note** The filtration is a record of information available before fresh sampling, augmented by the current committed loss, rather than the learner's post-revelation filtration from Section 2. Conditional equality on all such events expresses independence from fresh current sampling without exposing the learner's private future random bits to the adversary.
-- source:
--   Mengxiao Zhang, STOC 2027 submission #57 (October 2026), printed p. 3 / PDF p. 4, Section 2 nonanticipation; Algorithm 2 Option II, printed p. 11 / PDF p. 12; Eq. (20) proof, printed p. 13 / PDF p. 14; SHA-256 6db5a23e9e92d250b4dea7995bf34c9930d39a95df90f5d3fdc715ca26044f31

import Mathlib
import Definitions.Def_MinimaxAltRegret_Main_Continuous

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace MinimaxAltRegret.Main

/-- A stochastic realization of the exact Option II update. The pre-sampling filtration
contains all past actions/losses AND the already committed current loss. The event-law
identity is the conditional distribution of the action, so the adversary cannot see fresh
round-t randomness. It is a sampling rule, with no regret inequality in its fields.
Functions on X retain arbitrary boundary values; random regret is required measurable
so that its bounded expectation has its usual meaning. -/
structure SampledRun {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (X : Set (Point d)) (T : ℕ)
    (f : ℕ → Ω → Point d → ℝ) (x : ℕ → Ω → X) where
  before : Filtration ℕ mΩ
  losses : ∀ ω, convexLosses X T (fun s => f s ω)
  committed : ∀ t < T, Measurable[before t] (f t)
  past_losses : ∀ t ≤ T, ∀ s < t, Measurable[before t] (f s)
  past_actions : ∀ t ≤ T, ∀ s < t, Measurable[before t] (x s)
  actions_measurable : ∀ t ≤ T, Measurable (x t)
  regret_measurable : AEStronglyMeasurable
    (fun ω => alternatingRegret X T (fun s => f s ω) (fun s => (x s ω).val)) μ
  sampling : ∀ t ≤ T, ∀ E : Set Ω, MeasurableSet[before t] E →
    ∀ B : Set (Point d), MeasurableSet B →
      μ (E ∩ {ω | (x t ω).val ∈ B}) =
        ∫⁻ ω in E, ∫⁻ y in B, ENNReal.ofReal
          (continuousDensity X T (fun s => f s ω) t y) ∂bodyMeasure X ∂μ

end MinimaxAltRegret.Main



-- Prove2me | Definitions.Def_AppliedSDE_SarkkaSolin_Ch05ProbabilityDefinitions
-- name    : AppliedSDE_SarkkaSolin_Ch05ProbabilityDefinitions
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-13T17:53:18.933196+00:00
-- url     : https://prove2.me/theorems/1fd0ce30-f57f-4278-9ca0-6922fa889bfd
-- title:
--   Martingale, Markov process and scalar diffusion generators
-- statement:
--   Definition 5.1: an integrable, adapted martingale with conditional expectation equal to its earlier value. Definition 5.2: a transition generator as the right-hand limit of transition-semigroup expectations and the one-dimensional diffusion differential operator. Definition 5.3: generalized time-dependent scalar generator including the temporal derivative. Definition 5.9: the conditional expectation of future observables given the past equals that given the present state. These are source interfaces, and validity for a particular SDE requires proofs.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   \mathbb E[M_t\mid\mathcal F_s]=M_s\quad(0\leq s\leq t)
--   $$
-- source:
--   Original derived from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Definitions 5.1, 5.2, 5.3 and 5.9, printed pp. 59–67. https://doi.org/10.1017/9781108186735

import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace AppliedSDE.SarkkaSolin

/-- Definition 5.1, integrable adapted martingale relative to a filtration. -/
def IsMartingaleFor
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ℱ : Filtration (ℝ≥0) (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ t, Integrable (X t) P ∧ Measurable[ℱ t] (X t)) ∧
    ∀ s t, s ≤ t → P[X t | ℱ s] =ᵐ[P] X s

/-- Definition 5.2, limit definition for a transition-semigroup generator.
This is an operator/domain predicate; the differential expression is below. -/
def IsTransitionGenerator
    (transition : ℝ → ℝ → Measure ℝ)
    (A : (ℝ → ℝ) → ℝ → ℝ)
    (φ : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, Tendsto
    (fun h : ℝ =>
      ((∫ y : ℝ, φ y ∂transition h x) - φ x) / h)
    (𝓝[>] (0 : ℝ)) (𝓝 (A φ x))

/-- Definition 5.2, one-dimensional diffusion generator formula (5.5). -/
noncomputable def scalarDiffusionGenerator
    (b a φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  b x * deriv φ x +
    a x / 2 * deriv (fun y : ℝ => deriv φ y) x

/-- Definition 5.3, generalized time-dependent diffusion generator (5.9). -/
noncomputable def scalarTimeDiffusionGenerator
    (b a : ℝ → ℝ → ℝ) (φ : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  deriv (fun s : ℝ => φ s x) t +
    b t x * deriv (fun y : ℝ => φ t y) x +
    a t x / 2 *
      deriv (fun y : ℝ => deriv (fun z : ℝ => φ t z) y) x

/-- Definition 5.9: past and future conditional expectations factor
through the present state, for integrable bounded Borel observables. -/
def IsMarkovFor
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω)
    (ℱ : Filtration (ℝ≥0) (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → S) : Prop :=
  ∀ (s t : ℝ≥0), s ≤ t →
    ∀ (φ : S → ℝ), Measurable φ →
      Integrable (fun ω : Ω => φ (X t ω)) P →
      P[(fun ω : Ω => φ (X t ω)) | ℱ s] =ᵐ[P]
        P[(fun ω : Ω => φ (X t ω)) |
          MeasurableSpace.comap (X s) inferInstance]

end AppliedSDE.SarkkaSolin



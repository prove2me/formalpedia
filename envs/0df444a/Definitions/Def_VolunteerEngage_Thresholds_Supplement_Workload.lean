-- Prove2me | Definitions.Def_VolunteerEngage_Thresholds_Supplement_Workload
-- name    : VolunteerEngage_Thresholds_Supplement_Workload
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T04:11:29.507772+00:00
-- url     : https://prove2.me/theorems/f917f0c7-605c-4e7b-ba86-6aeb8459e301
-- title:
--   The reflected workload (54)–(57) and extended expected average cost (53)
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, $\mathbb F$ a filtration and $X$ a $(0,\sigma^2)$ Brownian motion for it, started at zero. Under a stationary Markov policy $\theta$, the adapted workload $W$ and regulator $U$ satisfy, simultaneously almost surely for every $t\ge0$,
--
--   $$W(t)=X(t)+\int_0^t\theta(W(s))\,ds-\int_0^t\kappa W(s)\,ds+U(t),\qquad W(t)\ge0,$$
--
--   where $U$ is nondecreasing, right-continuous, $U(0)=0$, and its Lebesgue–Stieltjes measure assigns no mass to $\{s\in[0,t]:W(s)>0\}$. Workload paths are continuous; the equations imply $W(0)=0$. For $t>0$ define
--
--   $$a_\theta(t)=\frac1t\mathbb E\!\left[\int_0^t c(\theta(W(s)))\,ds+pU(t)\right]\in[0,\infty].$$
--
--   The objective (53) is $\limsup_{t\to\infty}a_\theta(t)$. The predicate describes every solution; it constructs no solution map and asserts neither existence nor uniqueness, which the paper defers to the literature.
--
--   **Formalization Note** The general Brownian motion is the published `AtaBarjesteh23.Workload.IsDriftBM`. The regulator is represented by a Stieltjes function equal to $U$ at nonnegative times and zero at negative times, so there is no atom at zero. Continuous workload paths follow from the reflected equations. For a policy with values in $A$ the time integrands are measurable and bounded on compact intervals; no moment or transversality condition is added. Cost uses a nonnegative extended integral of the nonnegative path cost, avoiding default-zero expectations of nonintegrable functions. Values at nonpositive averaging times are irrelevant to the objective.
-- source:
--   Ata, Tongarlak, Lee, Field, A Dynamic Model for Managing Volunteer Engagement, arXiv:2312.02920v2, p. 19, (53)–(57); p. 17, Brownian motion following (49); p. 12, empty initial list

import Mathlib
import Definitions.Def_VolunteerEngage_Thresholds_Supplement_Admissible
import Definitions.Def_AtaBarjesteh23_Workload_DriftBM

namespace VolunteerEngage.Thresholds.Supplement

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Equations (54)–(57), simultaneously almost surely. The regulator's
Stieltjes function is its extension by zero to negative times; it therefore
has no artificial atom at zero. Continuous workload paths are a consequence
of the reflected equation. No moment or transversality premise is included. -/
def IsWorkload {Ω : Type*} [mΩ : MeasurableSpace Ω] (M : Model)
    (P : Measure Ω) (𝔽 : Filtration ℝ mΩ) (θ : ℝ → ℝ)
    (X W U : ℝ → Ω → ℝ) : Prop :=
  AtaBarjesteh23.Workload.IsDriftBM 𝔽 P X 0 M.σ ∧
  (∀ t : ℝ, 0 ≤ t → StronglyMeasurable[𝔽 t] (W t) ∧ StronglyMeasurable[𝔽 t] (U t)) ∧
  ∀ᵐ ω ∂P,
    ContinuousOn (fun t => W t ω) (Set.Ici 0) ∧
    U 0 ω = 0 ∧
    (∃ R : StieltjesFunction ℝ,
      (∀ s : ℝ, R s = if s < 0 then 0 else U s ω) ∧
      ∀ t : ℝ, 0 ≤ t → R.measure {s : ℝ | s ∈ Set.Icc 0 t ∧ 0 < W s ω} = 0) ∧
    ∀ t : ℝ, 0 ≤ t →
      0 ≤ W t ω ∧
      W t ω = X t ω + (∫ s in (0 : ℝ)..t, θ (W s ω)) -
        (∫ s in (0 : ℝ)..t, M.κ * W s ω) + U t ω

/-- Expected average cost (53), in [0,∞]. On valid paths both terms are
nonnegative; finite-time integrability is not assumed to use this definition.
The arbitrary t=0 value is irrelevant to limits at infinity. -/
noncomputable def avgCost {Ω : Type*} [MeasurableSpace Ω] (M : Model)
    (P : Measure Ω) (θ : ℝ → ℝ) (W U : ℝ → Ω → ℝ) (t : ℝ) : ℝ≥0∞ :=
  (∫⁻ ω, ENNReal.ofReal ((∫ s in (0 : ℝ)..t, cost M (θ (W s ω))) + M.p * U t ω) ∂P) /
    ENNReal.ofReal t

end VolunteerEngage.Thresholds.Supplement



-- Prove2me | Definitions.Def_TechBreakthrough_IsWeakSolution
-- name    : TechBreakthrough_IsWeakSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:32:31.049287+00:00
-- url     : https://prove2.me/theorems/cc50d1ad-7ad0-49df-92d7-1c06b1d8bbfa
-- title:
--   Weak solution of $dX=\mu(X)\,dt+\sigma(X)\,dW$ on the canonical space
-- statement:
--   A probability measure $P$ on the canonical space is the law of a weak solution of
--
--   $$dX_t=\mu(X_t)\,dt+\sigma(X_t)\,dW_t,\qquad X_0=x,$$
--
--   when $X_0=x$ almost surely and there are a filtration and a Brownian motion $B$ for that filtration, on the canonical space, such that $X$ and $B$ are adapted, future increments of $B$ are independent of the filtration, and for each $t$, almost surely,
--
--   $$X_t=x+\int_0^t\mu(X_s)\,ds+\int_0^t\sigma(X_s)\,dB_s.$$
--
--   **Formalization Note** The Itô integral is the published relation `EthierKurtz.HasBrownianItoIntegral`. Paths lie in $\mathcal I$ for every $\omega$. Since $\sigma>0$, the Brownian motion is recovered from $X$, so no enlargement of the canonical space is needed.
-- source:
--   Décamps, Gensbittel & Mariotti, Investment Timing and Technological Breakthroughs, arXiv:2106.05112v1, (7), p.9

import Definitions.Def_TechBreakthrough_PathSpace
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TechBreakthrough

/-- `P` is the law on the canonical space of a weak solution of the SDE (7),
`dX_t = μ(X_t) dt + σ(X_t) dW_t`, started at `x`, arXiv:2106.05112v1, §4.1, p.9.

The stochastic integral is the published relation `EthierKurtz.HasBrownianItoIntegral`
(predictable dyadic step approximations, convergence in probability).

**Formalization Note** The driving Brownian motion is carried by the canonical space itself. This
loses nothing: since `σ > 0`, it is recovered from `X` as `∫ σ(X)⁻¹ (dX − μ(X) dt)`. Paths are
continuous in `𝓘` for every `ω`, and the identity holds almost surely for each `t`. -/
structure IsWeakSolution {α β : EReal} (μ σ : ℝ → ℝ) (P : Measure (PathSpace α β)) (x : ℝ) :
    Prop where
  isProbabilityMeasure : IsProbabilityMeasure P
  initial : ∀ᵐ ω ∂P, canonicalProcess α β 0 ω = x
  driven : ∃ (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace (PathSpace α β)))
      (B J : ℝ≥0 → PathSpace α β → ℝ),
    Adapted ℱ (canonicalProcess α β) ∧ Adapted ℱ B ∧ IsBrownianReal B P ∧
    (∀ s t : ℝ≥0, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (ℱ s) P) ∧
    EthierKurtz.HasBrownianItoIntegral P (fun t => ℱ t) B
      (fun t ω => σ (canonicalProcess α β t ω)) J ∧
    ∀ t : ℝ≥0, ∀ᵐ ω ∂P, canonicalProcess α β t ω =
      x + (∫ s in (0 : ℝ)..(t : ℝ), μ (canonicalProcess α β s.toNNReal ω)) + J t ω

end TechBreakthrough



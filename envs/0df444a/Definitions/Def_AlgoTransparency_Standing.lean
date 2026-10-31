-- Prove2me | Definitions.Def_AlgoTransparency_Standing
-- name    : AlgoTransparency_Standing
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:49:05.112255+00:00
-- url     : https://prove2.me/theorems/944f834f-b993-4ffb-b0a2-48e7ff46c2a8
-- title:
--   Standing assumptions: $0<\theta<1$, $\lambda\in[1/2,1]$, Assumptions 1–3
-- statement:
--   The standing assumptions of the paper are:
--
--   1. $0<\theta<1$;
--   2. $\lambda\in[\tfrac12,1]$;
--   3. **Assumption 1:** $0<\beta<R<\alpha$;
--   4. **Assumption 2:** $\dfrac{(\theta\lambda+(1-\theta)(1-\lambda))R}{\theta\lambda}<\alpha<\dfrac{R}{\theta}$;
--   5. **Assumption 3:** $R-\theta\alpha<\beta<R-\dfrac{\theta(1-\lambda)\alpha}{\theta(1-\lambda)+(1-\theta)\lambda}$.
--
--   Every theorem of the mission assumes them. Assumption 1 makes the firm want to hire exactly the H agents; Assumptions 2 and 3 exclude trivial equilibria (App. A.3).
--
--   **Formalization Note** The paper never writes $0<\theta<1$, but it calls $\theta$ and $1-\theta$ portions and divides by both. The earlier conjuncts make the denominators in Assumptions 2 and 3 positive, so the divisions are the real ones. Assumption 2 forces $\lambda>\tfrac12$, since its two bounds coincide at $\lambda=\tfrac12$.
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, §3, pp.11–12 (PDF 12–13, θ and λ ∈ [0.5, 1]); §3.3, pp.15–16 (PDF 16–17), Assumptions 1–3

import Mathlib
import Definitions.Def_AlgoTransparency_Params

namespace AlgoTransparency

/-- **Standing assumptions** of Wang, Huang, Jasin & Singh, arXiv:2008.09283v1, §3 and §3.3,
pp.11–12, 15–16 (PDF 12–13, 16–17):

1. `0 < θ < 1` (the shares `θ` and `1 − θ` of the two types, p.11);
2. `λ ∈ [1/2, 1]` (p.12, "λ ∈ [0.5, 1]");
3. **Assumption 1** (p.15): `0 < β < R < α`;
4. **Assumption 2** (p.16): `(θλ + (1 − θ)(1 − λ))R/(θλ) < α < R/θ`;
5. **Assumption 3** (p.16): `R − θα < β < R − θ(1 − λ)α/(θ(1 − λ) + (1 − θ)λ)`.

**Formalization Note.** The paper never writes `0 < θ < 1`, but it calls `θ` and `1 − θ`
"portions" and divides by both; the open interval is the reading. The divisions in Assumptions
2 and 3 are taken literally: the earlier conjuncts make their denominators `θλ` and
`θ(1 − λ) + (1 − θ)λ` positive, so no junk value of `/` is ever reached when the predicate
holds. Assumption 2 forces `λ > 1/2` (its two bounds coincide at `λ = 1/2`); this is not added
as a separate conjunct. -/
def Standing (p : Params) : Prop :=
  (0 < p.θ ∧ p.θ < 1) ∧
  (1 / 2 ≤ p.lam ∧ p.lam ≤ 1) ∧
  (0 < p.β ∧ p.β < p.R ∧ p.R < p.α) ∧
  ((p.θ * p.lam + (1 - p.θ) * (1 - p.lam)) * p.R / (p.θ * p.lam) < p.α ∧ p.α < p.R / p.θ) ∧
  (p.R - p.θ * p.α < p.β ∧
    p.β < p.R - p.θ * (1 - p.lam) * p.α / (p.θ * (1 - p.lam) + (1 - p.θ) * p.lam))

end AlgoTransparency



-- Prove2me | Definitions.Def_KashUpgrade_revenueAt
-- name    : KashUpgrade_revenueAt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:23:10.237764+00:00
-- url     : https://prove2.me/theorems/6d10c07b-6dcc-4815-90ad-29793ecbc3b2
-- title:
--   The expected revenue $\mathrm{Revenue}(\pi,t)$ at time $t$
-- statement:
--   The expected revenue of a policy at time $t$, over the $d$ cohorts present:
--   $$
--   \mathrm{Revenue}(\pi,t)=\int\bigl(x_{q_1(\pi,t,\theta),m_1(\pi,t,\theta)}+\dots+x_{q_d(\pi,t,\theta),m_d(\pi,t,\theta)}\bigr)f(\theta)\,d\theta .
--   $$
--
--   **Formalization Note** For fixed $t$ the integrand takes finitely many values, on pieces cut out by finitely many affine inequalities in $\theta$. So it is integrable and the integral is genuine for every real price vector.
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), p.11

import Mathlib
import Definitions.Def_KashUpgrade_customerState

namespace KashUpgrade

/-- **The expected revenue at time `t`.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), p.11:
`Revenue(π, t) = ∫ (x_{q₁, m₁} + x_{q₂, m₂} + … + x_{q_d, m_d}) f θ dθ`.

**Formalization Note** For fixed `t` only finitely many classes and experiences occur, so the
integrand takes finitely many values on pieces cut out by finitely many affine inequalities in `θ`.
It is bounded and measurable, and the Bochner integral is never the junk value of a non-integrable
function. -/
noncomputable def revenueAt (f : ℝ → ℝ) (S : Schedule) (d : ℕ) (c : ℝ) (x : ℕ → ℕ → ℝ)
    (t : ℕ) : ℝ :=
  ∫ θ, (∑ ℓ ∈ Finset.Icc 1 d,
    classPrice x (customerState S x c ℓ t θ).1 (customerState S x c ℓ t θ).2) * f θ

end KashUpgrade



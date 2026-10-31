-- Prove2me | Definitions.Def_KashUpgrade_typeSupport
-- name    : KashUpgrade_typeSupport
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:19:05.035624+00:00
-- url     : https://prove2.me/theorems/d0f8c3fd-1cb1-4670-a5dd-fb08a62daf2b
-- title:
--   The support $[0,\zeta]$ of the customer type
-- statement:
--   The interval of customer types: $[0,\zeta]$, or $[0,\zeta)$ if $\zeta=\infty$, for $\zeta\in(0,\infty]$.
--
--   **Formalization Note** $\zeta$ is an extended nonnegative real, and the condition $\theta\le\zeta$ always holds when $\zeta=\infty$.
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), Assumption 2, p.13

import Mathlib

namespace KashUpgrade

/-- **The support of the customer type.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), Assumption 2, p.13: the interval `[0, ζ]`, or
`[0, ζ)` if `ζ = ∞`.

**Formalization Note** `ζ` lives in `ℝ≥0∞`, and `ENNReal.ofReal θ ≤ ⊤` always holds, so `ζ = ⊤`
gives `[0, ∞)`. -/
def typeSupport (ζ : ENNReal) : Set ℝ :=
  {θ | 0 ≤ θ ∧ ENNReal.ofReal θ ≤ ζ}

end KashUpgrade



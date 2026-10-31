-- Prove2me | Definitions.Def_KashUpgrade_totalRevenue
-- name    : KashUpgrade_totalRevenue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:25:10.699049+00:00
-- url     : https://prove2.me/theorems/bdddd8ee-43bd-4088-b64a-9787f195cb05
-- title:
--   The total revenue $\mathrm{Revenue}(\pi)$
-- statement:
--   The total revenue of a policy, discounted at $\delta\in(0,1)$:
--   $$
--   \mathrm{Revenue}(\pi)=\sum_{t=1}^{\infty}\delta^t\,\mathrm{Revenue}(\pi,t).
--   $$
--
--   **Formalization Note** In Lean the sum of a non-summable series is $0$, so comparisons of total revenues in this mission are guarded by summability of the series.
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), p.11

import Mathlib
import Definitions.Def_KashUpgrade_discountedRevenue

namespace KashUpgrade

/-- **The total revenue of a policy.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), p.11: `Revenue(π) = ∑_{t=1}^∞ δ^t Revenue(π, t)`.

**Formalization Note** Lean's `tsum` of a non-summable series is `0`, so every comparison of total
revenues in this mission carries a `Summable (discountedRevenue …)` guard. -/
noncomputable def totalRevenue (f : ℝ → ℝ) (S : Schedule) (d : ℕ) (c δ : ℝ)
    (x : ℕ → ℕ → ℝ) : ℝ :=
  ∑' n, discountedRevenue f S d c δ x n

end KashUpgrade



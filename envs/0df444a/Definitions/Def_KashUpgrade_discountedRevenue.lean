-- Prove2me | Definitions.Def_KashUpgrade_discountedRevenue
-- name    : KashUpgrade_discountedRevenue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:24:20.254136+00:00
-- url     : https://prove2.me/theorems/bd937641-a133-4a01-bc2d-0c657d532541
-- title:
--   The revenue series $\delta^t\,\mathrm{Revenue}(\pi,t)$
-- statement:
--   The term $\delta^t\,\mathrm{Revenue}(\pi,t)$, $t\ge 1$, of the total revenue.
--
--   **Formalization Note** The series is indexed from $0$, its $n$-th term being the one of time $t=n+1$.
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), p.11

import Mathlib
import Definitions.Def_KashUpgrade_revenueAt

namespace KashUpgrade

/-- **The discounted revenue series.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), p.11: the term `δ^t Revenue(π, t)` of the total revenue
`Revenue(π) = ∑_{t=1}^∞ δ^t Revenue(π, t)`, indexed from `t = 1`, so the `n`-th term of this
function is the one of time `n + 1`. -/
noncomputable def discountedRevenue (f : ℝ → ℝ) (S : Schedule) (d : ℕ) (c δ : ℝ)
    (x : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  δ ^ (n + 1) * revenueAt f S d c x (n + 1)

end KashUpgrade



-- Prove2me | Definitions.Def_KashUpgrade_sliceRevenue
-- name    : KashUpgrade_sliceRevenue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:22:59.320538+00:00
-- url     : https://prove2.me/theorems/1886d245-3ed6-4b95-8327-519eb1038ddb
-- title:
--   The slice revenue $\mathrm{Revenue}_{[s_j,s_{j+1})}$
-- statement:
--   The revenue from customers who arrive in the periods $s_j,\dots,s_{j+1}-1$:
--   $$
--   \mathrm{Revenue}_{[s_j,s_{j+1})}:=\sum_{t=s_j}^{s_{j+1}+d-2}\delta^t\int\Bigl(\sum_{\ell=\max(1,t-s_{j+1}+2)}^{\min(t-s_j+1,d)}x_{q_\ell(\pi,t,\theta),m_\ell(\pi,t,\theta)}\Bigr)f(\theta)\,d\theta .
--   $$
--
--   **Formalization Note** The sum over $t$ runs over all of $\mathbb N$: the range of ages is empty outside the printed range of $t$. For the last introduction of a finite schedule $s_{j+1}=\infty$, and this is a series; it converges because finitely many classes give bounded prices.
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), (10), p.14

import Mathlib
import Definitions.Def_KashUpgrade_customerState
import Definitions.Def_KashUpgrade_sliceAges

namespace KashUpgrade

/-- **The revenue of slice `j`.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), (10), p.14:
`Revenue_[s_j, s_{j+1}) := ∑_{t=s_j}^{s_{j+1}+d-2} δ^t ∫ (∑_ℓ x_{q_ℓ, m_ℓ}) f θ dθ`, the revenue
from customers who arrive in the periods `s_j, …, s_{j+1} - 1`.

**Formalization Note** The sum runs over all of `ℕ`: the age range `sliceAges` is empty for
`t < s_j` and for `t > s_{j+1} + d - 2`, so this is the printed finite sum. For the last introduction
of a finite schedule `s_{j+1} = ∞` and it is a series, which converges because finitely many classes
give bounded prices. -/
noncomputable def sliceRevenue (f : ℝ → ℝ) (S : Schedule) (d : ℕ) (c δ : ℝ)
    (j : ℕ) (x : ℕ → ℕ → ℝ) : ℝ :=
  ∑' t, δ ^ t * ∫ θ, (∑ ℓ ∈ sliceAges S d j t,
    classPrice x (customerState S x c ℓ t θ).1 (customerState S x c ℓ t θ).2) * f θ

end KashUpgrade



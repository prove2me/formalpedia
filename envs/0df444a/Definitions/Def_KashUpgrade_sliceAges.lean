-- Prove2me | Definitions.Def_KashUpgrade_sliceAges
-- name    : KashUpgrade_sliceAges
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:21:16.468994+00:00
-- url     : https://prove2.me/theorems/8f2e93ca-6dd8-4d8a-9041-7c77fd59f868
-- title:
--   The customer ages present in slice $j$ at time $t$
-- statement:
--   The range of the inner sum of (10):
--   $$
--   \max(1,\ t-s_{j+1}+2)\ \le\ \ell\ \le\ \min(t-s_j+1,\ d),
--   $$
--   i.e. the ages at time $t$ of customers who arrived in the periods $s_j,\dots,s_{j+1}-1$ and are still in the system. If introduction $j+1$ does not exist, then $s_{j+1}=\infty$ and the lower end is $1$.
--
--   **Formalization Note** The two differences are written $t+2-s_{j+1}$ and $t+1-s_j$ in natural numbers. Their truncation agrees with the formula after the maximum, and gives an empty range for $t<s_j$.
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), (10), p.14

import Mathlib
import Definitions.Def_KashUpgrade_IsIntroduced

namespace KashUpgrade

/-- **The ages present in slice `j` at time `t`.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), (10), p.14: the range
`max(1, t - s_{j+1} + 2) ≤ ℓ ≤ min(t - s_j + 1, d)` of the inner sum, i.e. the customers in the
system at time `t` who arrived in the periods `s_j, …, s_{j+1} - 1`.

**Formalization Note** Written `t + 2 - s_{j+1}` and `t + 1 - s_j` so that the truncated subtraction
of `ℕ` agrees with the integer formula after the `max` and with an empty range before `s_j`. If
introduction `j + 1` does not exist, then `s_{j+1} = ∞` and the lower end is `1`. -/
noncomputable def sliceAges (S : Schedule) (d j t : ℕ) : Finset ℕ :=
  open Classical in
  Finset.Icc (if IsIntroduced S (j + 1) then max 1 (t + 2 - S.s (j + 1)) else 1)
    (min (t + 1 - S.s j) d)

end KashUpgrade



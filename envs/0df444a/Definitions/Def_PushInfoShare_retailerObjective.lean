-- Prove2me | Definitions.Def_PushInfoShare_retailerObjective
-- name    : PushInfoShare_retailerObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:45:02.721001+00:00
-- url     : https://prove2.me/theorems/542934d0-c65c-4861-b7e8-dc6275ef03a8
-- title:
--   Retailer's objective (2)
-- statement:
--   With the inverse demand (1),
--   $$p_i=a+\theta-\frac{1+\phi}{1+2\phi}q_i-\frac{\phi}{1+2\phi}q_{3-i},$$
--   and zero marginal costs, the retailer's objective at the forecast $m$ of $\theta$ and wholesale prices $w$ is
--   $$\sum_{i=1}^{2}\Bigl(a+m-\frac{1+\phi}{1+2\phi}q_i-\frac{\phi}{1+2\phi}q_{3-i}-w_i\Bigr)q_i.$$
--   The problem is unconstrained, as in (2).
-- source:
--   Jain, Sharing Demand Information with Retailer under Upstream Competition, SSRN:3388957 (PDF of 2021-04-25), eq. (1), p.7, eq. (2), p.10

import Mathlib

namespace PushInfoShare

/-- The objective of the retailer's problem (2), Jain, SSRN:3388957 (PDF of 2021-04-25), eq. (2),
p.10, with the inverse demand (1), p.7:
`∑ᵢ (a + m − (1+φ)/(1+2φ) qᵢ − φ/(1+2φ) q₃₋ᵢ − wᵢ) qᵢ`, where `m` is the retailer's forecast of `θ`.

**Formalization Note.** `1 - i` is the paper's `3 − i`. The quantities are unconstrained, as in
(2). Marginal costs are zero (p.7). -/
noncomputable def retailerObjective (a φ m : ℝ) (w q : Fin 2 → ℝ) : ℝ :=
  ∑ i : Fin 2, (a + m - (1 + φ) / (1 + 2 * φ) * q i - φ / (1 + 2 * φ) * q (1 - i) - w i) * q i

end PushInfoShare



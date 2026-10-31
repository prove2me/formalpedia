-- Prove2me | Definitions.Def_ReservationPolicy_Params_mu2
-- name    : ReservationPolicy_Params_mu2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:21:37.652775+00:00
-- url     : https://prove2.me/theorems/cbcc126d-e0e0-4717-aa4f-3656b8997eec
-- title:
--   The quantity $\mu_2$ (corrected: bracket in the first term)
-- statement:
--   The denominator factor of (56), corrected:
--   $$
--   \mu_2=16k(16k^2-3k-5k\alpha+\alpha)+\bigl[-3\alpha+8k(3-16k+10k\alpha)\bigr]\phi^2+(16k-3)(1-\alpha)\phi^4.
--   $$
--   **Formalization Note** The paper prints the first term as $16k(16k^2-3k-5k\alpha)+\alpha$. That is a misplaced bracket: at $k=1,\phi=\tfrac12,\alpha=\tfrac3{10},z=\tfrac25$ the maximizer of welfare is $\tfrac{63}{32786}$, which (56) gives with the term above, while the printed term gives $\tfrac{1953}{989326}$.
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), p.41

import Mathlib
import Definitions.Def_ReservationPolicy_Params

namespace ReservationPolicy

/-- The quantity `μ₂` in (56), corrected. Bao, Ni & Singh, SSRN 3772113 (May 30, 2023), p.41 (PDF 41).

**Formalization Note** The page prints the first term as `16k(16k² − 3k − 5kα) + α`, a misplaced
bracket; the correct term is `16k(16k² − 3k − 5kα + α)`. At `k = 1`, `ϕ = 1/2`, `α = 3/10`, `z = 2/5`
the maximizer of `U` is `63/32786`; (56) gives that with this `μ₂` and `1953/989326` with the
printed one. -/
noncomputable def Params.mu2 (P : Params) : ℝ :=
  16 * P.k * (16 * P.k ^ 2 - 3 * P.k - 5 * P.k * P.α + P.α) +
    (-3 * P.α + 8 * P.k * (3 - 16 * P.k + 10 * P.k * P.α)) * P.ϕ ^ 2 +
    (16 * P.k - 3) * (1 - P.α) * P.ϕ ^ 4

end ReservationPolicy



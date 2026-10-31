-- Prove2me | Definitions.Def_ReservationPolicy_Params_zPrime
-- name    : ReservationPolicy_Params_zPrime
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:21:36.449665+00:00
-- url     : https://prove2.me/theorems/87f54327-6b38-4a85-a241-5799047c620b
-- title:
--   Capacity threshold $z'$ (57) (corrected: denominator)
-- statement:
--   The capacity threshold of the paper's equation (57), corrected:
--   $$
--   z'=\frac{32k^2+\phi^2-8k(1-\alpha+\alpha\phi^2)}{3(32k^2+\phi^2)-16k(1+\phi^2)}.
--   $$
--   **Formalization Note** The paper prints the denominator $3(32k^2+\phi^2)+16(1+\phi^2)$, while solving $\mu_1=0$ for $z$ gives the one above. At $k=1,\phi=\tfrac12,\alpha=\tfrac3{10},z=\tfrac3{10}$ the printed threshold is $0.2231\ldots<z$, yet the maximizer of welfare is $0$; the corrected threshold is $\tfrac{521}{1535}$.
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eq. (57), p.41

import Mathlib
import Definitions.Def_ReservationPolicy_Params

namespace ReservationPolicy

/-- The capacity threshold `z'`, (57), corrected. Bao, Ni & Singh, SSRN 3772113 (May 30, 2023),
eq. (57), p.41 (PDF 41).

**Formalization Note** The page prints the denominator `3(32k² + ϕ²) + 16(1 + ϕ²)`; solving `μ₁ = 0`
for `z` gives `3(32k² + ϕ²) − 16k(1 + ϕ²)`. At `k = 1`, `ϕ = 1/2`, `α = 3/10`, `z = 3/10` the printed
threshold is below `z`, yet `μ₁ < 0` and the maximizer is `0`. -/
noncomputable def Params.zPrime (P : Params) : ℝ :=
  (32 * P.k ^ 2 + P.ϕ ^ 2 - 8 * P.k * (1 - P.α + P.α * P.ϕ ^ 2)) /
    (3 * (32 * P.k ^ 2 + P.ϕ ^ 2) - 16 * P.k * (1 + P.ϕ ^ 2))

end ReservationPolicy



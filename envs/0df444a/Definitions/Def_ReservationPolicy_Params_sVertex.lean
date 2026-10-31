-- Prove2me | Definitions.Def_ReservationPolicy_Params_sVertex
-- name    : ReservationPolicy_Params_sVertex
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:24:08.308691+00:00
-- url     : https://prove2.me/theorems/688fa7e7-2973-4ed8-93b4-054383ea82ff
-- title:
--   First-order solution (56)
-- statement:
--   The solution of the first-order condition for welfare, the paper's equation (56):
--   $$
--   \frac{(4k-1)(1-\alpha)\alpha(4k-\phi^2)(1-\phi^2)\mu_1}{(8k-1)(8k-\phi^2)\mu_2}.
--   $$
--   **Formalization Note** $\mu_2$ is the corrected `Params.mu2`. The paper calls this quantity $s^*$; it can be negative, and the optimal transfer is its positive part (`Params.sStar`).
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eq. (56), p.40

import Mathlib
import Definitions.Def_ReservationPolicy_Params_mu1
import Definitions.Def_ReservationPolicy_Params_mu2

namespace ReservationPolicy

/-- The first-order solution (56), with the corrected `μ₂`. Bao, Ni & Singh, SSRN 3772113
(May 30, 2023), eq. (56), p.40 (PDF 40). -/
noncomputable def Params.sVertex (P : Params) : ℝ :=
  (4 * P.k - 1) * (1 - P.α) * P.α * (4 * P.k - P.ϕ ^ 2) * (1 - P.ϕ ^ 2) * P.mu1 /
    ((8 * P.k - 1) * (8 * P.k - P.ϕ ^ 2) * P.mu2)

end ReservationPolicy



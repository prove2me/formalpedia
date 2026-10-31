-- Prove2me | Definitions.Def_ReservationPolicy_Params_dY
-- name    : ReservationPolicy_Params_dY
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:23:12.624501+00:00
-- url     : https://prove2.me/theorems/5945279f-2a7f-4da7-8e9f-cffb50418183
-- title:
--   Type-$y$ cutoff under a transfer (52)
-- statement:
--   The closed form of the paper's equation (52):
--   $$
--   d_y^*(s)=d^*-\frac{s(8k-\phi^2)}{(1-\alpha)(4k-\phi^2)}.
--   $$
--   That this is the type-$y$ cutoff under the policy is the theorem `eq_51_52`.
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eq. (52), p.39

import Mathlib
import Definitions.Def_ReservationPolicy_Params_dStar

namespace ReservationPolicy

/-- The closed form (52) of the type-`y` cutoff at transfer `s`. Bao, Ni & Singh, SSRN 3772113
(May 30, 2023), eq. (52), p.39 (PDF 39). -/
noncomputable def Params.dY (P : Params) (s : ℝ) : ℝ :=
  P.dStar - s * (8 * P.k - P.ϕ ^ 2) / ((1 - P.α) * (4 * P.k - P.ϕ ^ 2))

end ReservationPolicy



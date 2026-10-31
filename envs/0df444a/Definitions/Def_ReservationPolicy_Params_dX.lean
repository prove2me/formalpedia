-- Prove2me | Definitions.Def_ReservationPolicy_Params_dX
-- name    : ReservationPolicy_Params_dX
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:22:46.941098+00:00
-- url     : https://prove2.me/theorems/bef00429-f8f2-4c71-a06f-15ba413b538d
-- title:
--   Type-$x$ cutoff under a transfer (51)
-- statement:
--   The closed form of the paper's equation (51):
--   $$
--   d_x^*(s)=d^*+\frac{s(8k-1)}{\alpha(4k-1)}.
--   $$
--   That this is the type-$x$ cutoff under the policy is the theorem `eq_51_52`.
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eq. (51), p.39

import Mathlib
import Definitions.Def_ReservationPolicy_Params_dStar

namespace ReservationPolicy

/-- The closed form (51) of the type-`x` cutoff at transfer `s`. Bao, Ni & Singh, SSRN 3772113
(May 30, 2023), eq. (51), p.39 (PDF 39). -/
noncomputable def Params.dX (P : Params) (s : ℝ) : ℝ :=
  P.dStar + s * (8 * P.k - 1) / (P.α * (4 * P.k - 1))

end ReservationPolicy



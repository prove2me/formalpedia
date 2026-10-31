-- Prove2me | Definitions.Def_ReservationPolicy_Params_sStar
-- name    : ReservationPolicy_Params_sStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:25:42.372794+00:00
-- url     : https://prove2.me/theorems/25936b8e-a74a-4ca1-9311-b266ff35d709
-- title:
--   Welfare-maximizing transfer in closed form
-- statement:
--   The closed form of the optimal transfer: the positive part of (56),
--   $$
--   s^*=\max\{0,\ \text{(56)}\},
--   $$
--   in line with p.41: "Therefore, if $z>z'$, $0<s^*<1$. Otherwise, $s^*=0$."
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), p.41

import Mathlib
import Definitions.Def_ReservationPolicy_Params_sVertex

namespace ReservationPolicy

/-- The closed form of the welfare-maximizing transfer: (56) when it is positive and `0` otherwise,
as p.41 says ("Otherwise, s* = 0"). Bao, Ni & Singh, SSRN 3772113 (May 30, 2023), p.41 (PDF 41). -/
noncomputable def Params.sStar (P : Params) : ℝ :=
  max 0 P.sVertex

end ReservationPolicy



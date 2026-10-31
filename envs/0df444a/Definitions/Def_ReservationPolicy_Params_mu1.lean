-- Prove2me | Definitions.Def_ReservationPolicy_Params_mu1
-- name    : ReservationPolicy_Params_mu1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:22:59.181323+00:00
-- url     : https://prove2.me/theorems/57f42d00-af8c-473d-8328-3e3774f9c09c
-- title:
--   The quantity $\mu_1$
-- statement:
--   The numerator factor of (56):
--   $$
--   \mu_1=16k\bigl[2k-d^*(6k-1)\bigr]+\bigl[(16k-3)d^*-1\bigr]\phi^2.
--   $$
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), p.41

import Mathlib
import Definitions.Def_ReservationPolicy_Params_dStar

namespace ReservationPolicy

/-- The quantity `μ₁` in (56). Bao, Ni & Singh, SSRN 3772113 (May 30, 2023), p.41 (PDF 41). -/
noncomputable def Params.mu1 (P : Params) : ℝ :=
  16 * P.k * (2 * P.k - P.dStar * (6 * P.k - 1)) + ((16 * P.k - 3) * P.dStar - 1) * P.ϕ ^ 2

end ReservationPolicy



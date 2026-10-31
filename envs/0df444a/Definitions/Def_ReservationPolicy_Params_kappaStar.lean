-- Prove2me | Definitions.Def_ReservationPolicy_Params_kappaStar
-- name    : ReservationPolicy_Params_kappaStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:20:57.071995+00:00
-- url     : https://prove2.me/theorems/557e1362-58eb-467c-86db-063be071ffbf
-- title:
--   Threshold $\kappa^*$ (32)
-- statement:
--   The threshold of the paper's equation (32):
--   $$
--   \kappa^*=\frac{k(1-z)^2(1-\phi^2)(8k-\phi^2)^2}{\bigl(\phi^2+4k(8k-1-\alpha-(2-\alpha)\phi^2)\bigr)^2}.
--   $$
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eq. (32), p.36

import Mathlib
import Definitions.Def_ReservationPolicy_Params

namespace ReservationPolicy

/-- The threshold `κ*`, (32): the largest cost at which investing is not deviated from. Bao, Ni &
Singh, SSRN 3772113 (May 30, 2023), eq. (32), p.36 (PDF 36). -/
noncomputable def Params.kappaStar (P : Params) : ℝ :=
  P.k * (1 - P.z) ^ 2 * (1 - P.ϕ ^ 2) * (8 * P.k - P.ϕ ^ 2) ^ 2 /
    (P.ϕ ^ 2 + 4 * P.k * (8 * P.k - 1 - P.α - (2 - P.α) * P.ϕ ^ 2)) ^ 2

end ReservationPolicy



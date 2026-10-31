-- Prove2me | Definitions.Def_ReservationPolicy_Params_kappaDoubleHat
-- name    : ReservationPolicy_Params_kappaDoubleHat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:21:02.839134+00:00
-- url     : https://prove2.me/theorems/67aa7a0d-d2fd-43ef-8377-43d0ff6f20b5
-- title:
--   Threshold $\hat{\hat\kappa}$ (45)
-- statement:
--   The threshold of the paper's equation (45), written with a double hat:
--   $$
--   \hat{\hat\kappa}=\frac{k(1-z)^2(1-\phi^2)}{(4k-\phi^2)^2}.
--   $$
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eq. (45), p.37

import Mathlib
import Definitions.Def_ReservationPolicy_Params

namespace ReservationPolicy

/-- The threshold with the double hat, (45). Bao, Ni & Singh, SSRN 3772113 (May 30, 2023), eq. (45),
p.37 (PDF 37). -/
noncomputable def Params.kappaDoubleHat (P : Params) : ℝ :=
  P.k * (1 - P.z) ^ 2 * (1 - P.ϕ ^ 2) / (4 * P.k - P.ϕ ^ 2) ^ 2

end ReservationPolicy



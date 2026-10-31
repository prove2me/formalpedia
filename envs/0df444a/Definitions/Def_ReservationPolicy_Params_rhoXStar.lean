-- Prove2me | Definitions.Def_ReservationPolicy_Params_rhoXStar
-- name    : ReservationPolicy_Params_rhoXStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:21:37.730398+00:00
-- url     : https://prove2.me/theorems/047c5562-9435-4baa-acbb-155529f1adbe
-- title:
--   Closed form of $\rho_x^*$ (28)
-- statement:
--   The first case of the paper's equation (28):
--   $$
--   \rho_x^*=\frac{32k^2z+z\phi^2+4k(1-\alpha)(1-\phi^2)-4kz(2+\phi^2)}{32k^2+\phi^2-4k[1+2\phi^2+\alpha(1-\phi^2)]}.
--   $$
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eq. (28), p.35

import Mathlib
import Definitions.Def_ReservationPolicy_Params

namespace ReservationPolicy

/-- The closed form (28) of the type-`x` equilibrium admission probability. Bao, Ni & Singh,
SSRN 3772113 (May 30, 2023), eq. (28), p.35 (PDF 35). -/
noncomputable def Params.rhoXStar (P : Params) : ℝ :=
  (32 * P.k ^ 2 * P.z + P.z * P.ϕ ^ 2 + 4 * P.k * (1 - P.α) * (1 - P.ϕ ^ 2) -
      4 * P.k * P.z * (2 + P.ϕ ^ 2)) /
    (32 * P.k ^ 2 + P.ϕ ^ 2 - 4 * P.k * (1 + 2 * P.ϕ ^ 2 + P.α * (1 - P.ϕ ^ 2)))

end ReservationPolicy



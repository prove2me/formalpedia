-- Prove2me | Definitions.Def_ReservationPolicy_Params_sZero
-- name    : ReservationPolicy_Params_sZero
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:21:39.376119+00:00
-- url     : https://prove2.me/theorems/59e1195e-1ced-476d-9d75-e3be3643f75b
-- title:
--   Inequality-eliminating transfer $s_0$ (24)
-- statement:
--   The closed form of the paper's equation (24):
--   $$
--   s_0=\frac{4k\alpha(1-z)(1-\alpha)(1-\phi^2)}{32k^2+\phi^2-4k\bigl(1+2\phi^2+\alpha(1-\phi^2)\bigr)}.
--   $$
--   What $s_0$ achieves is the content of Proposition 6.
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eq. (24), p.24

import Mathlib
import Definitions.Def_ReservationPolicy_Params

namespace ReservationPolicy

/-- The transfer `s₀`, (24). Bao, Ni & Singh, SSRN 3772113 (May 30, 2023), eq. (24), p.24 (PDF 24). -/
noncomputable def Params.sZero (P : Params) : ℝ :=
  4 * P.k * P.α * (1 - P.z) * (1 - P.α) * (1 - P.ϕ ^ 2) /
    (32 * P.k ^ 2 + P.ϕ ^ 2 - 4 * P.k * (1 + 2 * P.ϕ ^ 2 + P.α * (1 - P.ϕ ^ 2)))

end ReservationPolicy



-- Prove2me | Definitions.Def_ReservationPolicy_Params_kappaTilde
-- name    : ReservationPolicy_Params_kappaTilde
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:21:02.566392+00:00
-- url     : https://prove2.me/theorems/33ea136d-3d12-4b7c-beec-709921864a20
-- title:
--   Threshold $\tilde\kappa$ (46)
-- statement:
--   The threshold of the paper's equation (46):
--   $$
--   \tilde\kappa=\frac{k(1-z)(8k-\phi^2)\bigl(\phi^2(3z+1-16k(1-\alpha+z))+8k((16k-3)z-2\alpha+1)\bigr)}{\bigl(4k(8k-\alpha-(2-\alpha)\phi^2-1)+\phi^2\bigr)^2}-\frac{k(1-z)(16kz-(3z+1)\phi^2)}{(4k-\phi^2)^2}.
--   $$
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eq. (46), p.37

import Mathlib
import Definitions.Def_ReservationPolicy_Params

namespace ReservationPolicy

/-- The threshold `κ̃`, (46). Bao, Ni & Singh, SSRN 3772113 (May 30, 2023), eq. (46), p.37 (PDF 37). -/
noncomputable def Params.kappaTilde (P : Params) : ℝ :=
  P.k * (1 - P.z) * (8 * P.k - P.ϕ ^ 2) *
      (P.ϕ ^ 2 * (3 * P.z + 1 - 16 * P.k * (1 - P.α + P.z)) +
        8 * P.k * ((16 * P.k - 3) * P.z - 2 * P.α + 1)) /
      (4 * P.k * (8 * P.k - P.α - (2 - P.α) * P.ϕ ^ 2 - 1) + P.ϕ ^ 2) ^ 2 -
    P.k * (1 - P.z) * (16 * P.k * P.z - (3 * P.z + 1) * P.ϕ ^ 2) / (4 * P.k - P.ϕ ^ 2) ^ 2

end ReservationPolicy



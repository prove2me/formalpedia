-- Prove2me | Definitions.Def_ReservationPolicy_Params_dStar
-- name    : ReservationPolicy_Params_dStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:21:33.696544+00:00
-- url     : https://prove2.me/theorems/660b8b61-e131-4793-b7af-eaceddba1d3c
-- title:
--   Equilibrium cutoff $d^*$ (26)
-- statement:
--   The closed form of the paper's equation (26):
--   $$
--   d^*=\frac{(8k-\phi^2)\bigl[(8k-1)(1-2z)+\alpha\bigr]+\phi^2(1-\alpha)(8k-1)}{(8k-\phi^2)(8k-1-\alpha)-\phi^2(1-\alpha)(8k-1)}.
--   $$
--   That this is the equilibrium cutoff is the theorem `eq_26_27`.
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eq. (26), p.35

import Mathlib
import Definitions.Def_ReservationPolicy_Params

namespace ReservationPolicy

/-- The cutoff `d*`, (26). Bao, Ni & Singh, SSRN 3772113 (May 30, 2023), eq. (26), p.35 (PDF 35). -/
noncomputable def Params.dStar (P : Params) : ℝ :=
  ((8 * P.k - P.ϕ ^ 2) * ((8 * P.k - 1) * (1 - 2 * P.z) + P.α) +
      P.ϕ ^ 2 * (1 - P.α) * (8 * P.k - 1)) /
    ((8 * P.k - P.ϕ ^ 2) * (8 * P.k - 1 - P.α) - P.ϕ ^ 2 * (1 - P.α) * (8 * P.k - 1))

end ReservationPolicy



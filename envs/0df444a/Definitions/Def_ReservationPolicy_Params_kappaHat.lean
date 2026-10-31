-- Prove2me | Definitions.Def_ReservationPolicy_Params_kappaHat
-- name    : ReservationPolicy_Params_kappaHat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:23:28.436379+00:00
-- url     : https://prove2.me/theorems/08abd4fa-ff90-4853-a910-85a84b932ad6
-- title:
--   Threshold $\hat\kappa=\min\{\hat{\hat\kappa},\tilde\kappa\}$
-- statement:
--   The threshold of Proposition 1 is $\hat\kappa=\min\{\hat{\hat\kappa},\tilde\kappa\}$, defined on p.37.
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), p.37

import Mathlib
import Definitions.Def_ReservationPolicy_Params_kappaDoubleHat
import Definitions.Def_ReservationPolicy_Params_kappaTilde

namespace ReservationPolicy

/-- The threshold `κ̂ = min{κ̂̂, κ̃}` of Proposition 1. Bao, Ni & Singh, SSRN 3772113 (May 30, 2023),
p.37 (PDF 37). -/
noncomputable def Params.kappaHat (P : Params) : ℝ :=
  min P.kappaDoubleHat P.kappaTilde

end ReservationPolicy



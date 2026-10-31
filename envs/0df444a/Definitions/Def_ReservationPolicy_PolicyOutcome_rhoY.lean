-- Prove2me | Definitions.Def_ReservationPolicy_PolicyOutcome_rhoY
-- name    : ReservationPolicy_PolicyOutcome_rhoY
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:22:59.6676+00:00
-- url     : https://prove2.me/theorems/0c5f49ad-8aec-40c8-bcfd-882bd0f58307
-- title:
--   Type-$y$ admission probability under the policy
-- statement:
--   Under the policy a type-$y$ student has admission probability $\rho_{y,s}=\rho(\phi e_{y,s},d_y)$.
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eq. (21), p.20

import Mathlib
import Definitions.Def_ReservationPolicy_PolicyOutcome
import Definitions.Def_ReservationPolicy_Params
import Definitions.Def_ReservationPolicy_admitProb

namespace ReservationPolicy

/-- The admission probability of a type-`y` student under the policy. Bao, Ni & Singh, SSRN 3772113
(May 30, 2023), p.20 (PDF 20). -/
noncomputable def PolicyOutcome.rhoY (P : Params) (o : PolicyOutcome) : ℝ :=
  admitProb (P.ϕ * o.ey) o.dy

end ReservationPolicy



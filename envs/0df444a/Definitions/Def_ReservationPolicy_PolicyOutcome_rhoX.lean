-- Prove2me | Definitions.Def_ReservationPolicy_PolicyOutcome_rhoX
-- name    : ReservationPolicy_PolicyOutcome_rhoX
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:22:45.107053+00:00
-- url     : https://prove2.me/theorems/e7f866dc-892d-429e-9a8b-477022d07bbd
-- title:
--   Type-$x$ admission probability under the policy
-- statement:
--   Under the policy a type-$x$ student invests and has admission probability $\rho_{x,s}=\rho(e_{x,s},d_x)$.
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eq. (21), p.20

import Mathlib
import Definitions.Def_ReservationPolicy_PolicyOutcome
import Definitions.Def_ReservationPolicy_admitProb

namespace ReservationPolicy

/-- The admission probability of a type-`x` student under the policy, type `x` investing.
Bao, Ni & Singh, SSRN 3772113 (May 30, 2023), p.20 (PDF 20). -/
noncomputable def PolicyOutcome.rhoX (o : PolicyOutcome) : ℝ :=
  admitProb o.ex o.dx

end ReservationPolicy



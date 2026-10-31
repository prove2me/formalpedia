-- Prove2me | Definitions.Def_ReservationPolicy_welfare
-- name    : ReservationPolicy_welfare
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:23:13.744983+00:00
-- url     : https://prove2.me/theorems/858d9e39-7d87-47dd-b437-4ea73dfdbe88
-- title:
--   Overall student welfare $U$
-- statement:
--   Overall student welfare at an outcome under the policy is
--   $$
--   U=\alpha\,u_{x,s}+(1-\alpha)\,u_{y,s},
--   $$
--   where $u_{x,s}$ and $u_{y,s}$ are the expected payoffs of the two types, $u_{x,s}$ net of $\kappa$. The closed form is the theorem `eq_55`.
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eq. (55), p.40

import Mathlib
import Definitions.Def_ReservationPolicy_payoffInvest
import Definitions.Def_ReservationPolicy_payoffPlain
import Definitions.Def_ReservationPolicy_PolicyOutcome

namespace ReservationPolicy

/-- Overall student welfare at an outcome under the policy: the size-weighted payoffs of the two
types, the type-`x` payoff being net of `κ`. Bao, Ni & Singh, SSRN 3772113 (May 30, 2023), eq. (55),
p.40 (PDF 40). -/
noncomputable def welfare (P : Params) (o : PolicyOutcome) : ℝ :=
  P.α * payoffInvest P o.dx o.rx o.ex + (1 - P.α) * payoffPlain P o.dy o.ry o.ey

end ReservationPolicy



-- Prove2me | Definitions.Def_ReservationPolicy_EI
-- name    : ReservationPolicy_EI
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:24:50.247022+00:00
-- url     : https://prove2.me/theorems/2cb9098e-3472-41f9-93b6-e31b2d70aa45
-- title:
--   Educational inequality under the policy
-- statement:
--   Educational inequality is the difference of the equilibrium admission probabilities of the two types:
--   $$
--   EI=\rho_{x,s}-\rho_{y,s}.
--   $$
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eqs. (3), (58), pp.10, 41

import Mathlib
import Definitions.Def_ReservationPolicy_PolicyOutcome_rhoX
import Definitions.Def_ReservationPolicy_PolicyOutcome_rhoY

namespace ReservationPolicy

/-- Educational inequality at an outcome under the policy: the type-`x` minus the type-`y` admission
probability. Bao, Ni & Singh, SSRN 3772113 (May 30, 2023), eqs. (3), (58), pp.10, 41 (PDF 10, 41). -/
noncomputable def EI (P : Params) (o : PolicyOutcome) : ℝ :=
  o.rhoX - o.rhoY P

end ReservationPolicy



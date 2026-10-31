-- Prove2me | Definitions.Def_ReservationPolicy_payoffInvest
-- name    : ReservationPolicy_payoffInvest
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:22:21.070691+00:00
-- url     : https://prove2.me/theorems/6a039852-8030-44e3-a753-944c6bcb9b77
-- title:
--   Payoff of a type-$x$ student who invests
-- statement:
--   A type-$x$ student who invests $\kappa$ and exerts effort $e$, facing cutoff $d$ and reward $r$, has expected payoff
--   $$
--   \rho(e,d)\,r-ke^2-\kappa .
--   $$
--   The student takes $d$ and $r$ as given.
--
--   **Formalization Note** $\rho$ is the true admission probability `admitProb`, which equals the paper's $(1-d+e)/2$ when $|d-e|<1$.
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eqs. (5), (8), (17), pp.11–12, 19

import Mathlib
import Definitions.Def_ReservationPolicy_Params
import Definitions.Def_ReservationPolicy_admitProb

namespace ReservationPolicy

/-- The expected payoff of a student who invests `κ` and exerts effort `e`, given the cutoff `d` and
the reward `r`. Bao, Ni & Singh, SSRN 3772113 (May 30, 2023), eqs. (5), (8), (17), pp.11, 12, 19
(PDF 11, 12, 19). -/
noncomputable def payoffInvest (P : Params) (d r e : ℝ) : ℝ :=
  admitProb e d * r - P.k * e ^ 2 - P.κ

end ReservationPolicy



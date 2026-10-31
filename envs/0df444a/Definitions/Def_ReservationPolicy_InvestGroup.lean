-- Prove2me | Definitions.Def_ReservationPolicy_InvestGroup
-- name    : ReservationPolicy_InvestGroup
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:23:13.881088+00:00
-- url     : https://prove2.me/theorems/736f1a17-fefd-4fd9-8bc6-6486e01d2d37
-- title:
--   Effort and reward of an investing group
-- statement:
--   A common effort $e$ and reward $r$ of a group of investing students at cutoff $d$ are consistent when
--
--   1. $e$ maximizes the payoff $\rho(e',d)r-ke'^2-\kappa$ over the efforts of `investEfforts`, with $d$ and $r$ taken as given;
--   2. the reward equals the expected ability of the admitted students of the group, $r=E[e+\varepsilon\mid e+\varepsilon>d]$.
--
--   This is one half of the rational-expectations equilibrium of the paper.
--
--   **Formalization Note** Membership in `investEfforts` forces the group's admission probability into $(0,1)$.
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eqs. (9)–(10), pp.12–13

import Mathlib
import Definitions.Def_ReservationPolicy_payoffInvest
import Definitions.Def_ReservationPolicy_admittedMean
import Definitions.Def_ReservationPolicy_investEfforts

namespace ReservationPolicy

/-- A group of investing students at cutoff `d` with common effort `e` and reward `r`: `e` is a best
response to `(d, r)`, and `r` is the expected ability of the group's admitted students, which is
how the expectations of p.11 are fulfilled. Bao, Ni & Singh, SSRN 3772113 (May 30, 2023),
pp.11–13 (PDF 11–13). -/
def InvestGroup (P : Params) (e d r : ℝ) : Prop :=
  e ∈ investEfforts d ∧ (∀ e' ∈ investEfforts d, payoffInvest P d r e' ≤ payoffInvest P d r e) ∧
    r = admittedMean e d

end ReservationPolicy



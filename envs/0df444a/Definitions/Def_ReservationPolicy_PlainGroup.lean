-- Prove2me | Definitions.Def_ReservationPolicy_PlainGroup
-- name    : ReservationPolicy_PlainGroup
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:23:45.147343+00:00
-- url     : https://prove2.me/theorems/d4305a96-7066-4d30-a628-87f085e69029
-- title:
--   Effort and reward of a non-investing group
-- statement:
--   A common effort $e$ and reward $r$ of a group of non-investing students at cutoff $d$ are consistent when
--
--   1. $e$ maximizes the payoff $\rho(\phi e',d)r-ke'^2$ over the efforts of `plainEfforts`, with $d$ and $r$ taken as given;
--   2. the reward equals the expected ability of the admitted students of the group, $r=E[\phi e+\varepsilon\mid \phi e+\varepsilon>d]$.
--
--   **Formalization Note** Membership in `plainEfforts` forces the group's admission probability into $(0,1)$.
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eqs. (9)–(10), pp.12–13

import Mathlib
import Definitions.Def_ReservationPolicy_payoffPlain
import Definitions.Def_ReservationPolicy_admittedMean
import Definitions.Def_ReservationPolicy_plainEfforts

namespace ReservationPolicy

/-- A group of non-investing students at cutoff `d` with common effort `e` and reward `r`: `e` is a
best response to `(d, r)`, and `r` is the expected ability of the group's admitted students.
Bao, Ni & Singh, SSRN 3772113 (May 30, 2023), pp.11–13 (PDF 11–13). -/
def PlainGroup (P : Params) (e d r : ℝ) : Prop :=
  e ∈ plainEfforts P d ∧ (∀ e' ∈ plainEfforts P d, payoffPlain P d r e' ≤ payoffPlain P d r e) ∧
    r = admittedMean (P.ϕ * e) d

end ReservationPolicy



-- Prove2me | Definitions.Def_ReservationPolicy_NoInvestOptimal
-- name    : ReservationPolicy_NoInvestOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:23:24.747499+00:00
-- url     : https://prove2.me/theorems/ec779e60-9b46-41cb-8a49-4e4dbc8baad4
-- title:
--   Not investing beats investing at the first stage
-- statement:
--   A type-$x$ student who plans not to invest and to exert effort $e$ has no profitable deviation to investing when, for the given cutoff $d$ and reward $r$,
--   $$
--   \rho(e',d)\,r-ke'^2-\kappa\ \le\ \rho(\phi e,d)\,r-ke^2\qquad\text{for every } e' \text{ in } \texttt{investEfforts}.
--   $$
--   This is the deviation (42)–(43) of Case 2 of the proof of Proposition 1.
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eqs. (42)–(43), p.37

import Mathlib
import Definitions.Def_ReservationPolicy_payoffInvest
import Definitions.Def_ReservationPolicy_payoffPlain
import Definitions.Def_ReservationPolicy_investEfforts

namespace ReservationPolicy

/-- At the first stage a type-`x` student prefers not to invest: the payoff of not investing with
effort `e` is at least the payoff of investing with any effort, given `(d, r)`. Bao, Ni & Singh,
SSRN 3772113 (May 30, 2023), eqs. (42)–(43), p.37 (PDF 37). -/
def NoInvestOptimal (P : Params) (d r e : ℝ) : Prop :=
  ∀ e' ∈ investEfforts d, payoffInvest P d r e' ≤ payoffPlain P d r e

end ReservationPolicy



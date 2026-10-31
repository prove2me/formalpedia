-- Prove2me | Definitions.Def_ReservationPolicy_InvestOptimal
-- name    : ReservationPolicy_InvestOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:23:41.002492+00:00
-- url     : https://prove2.me/theorems/840963e1-f0db-42f6-b555-a53362c3442c
-- title:
--   Investing beats not investing at the first stage
-- statement:
--   A type-$x$ student who plans to invest and exert effort $e$ has no profitable deviation to not investing when, for the given cutoff $d$ and reward $r$,
--   $$
--   \rho(\phi e',d)\,r-ke'^2\ \le\ \rho(e,d)\,r-ke^2-\kappa\qquad\text{for every } e' \text{ in } \texttt{plainEfforts}.
--   $$
--   This is the deviation (30)–(31) of the proof of Proposition 1.
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eqs. (30)–(31), p.35

import Mathlib
import Definitions.Def_ReservationPolicy_payoffInvest
import Definitions.Def_ReservationPolicy_payoffPlain
import Definitions.Def_ReservationPolicy_plainEfforts

namespace ReservationPolicy

/-- At the first stage a type-`x` student prefers to invest: the payoff of investing with effort `e`
is at least the payoff of not investing with any effort, given `(d, r)`. Bao, Ni & Singh,
SSRN 3772113 (May 30, 2023), eqs. (30)–(31), p.35 (PDF 35). -/
def InvestOptimal (P : Params) (d r e : ℝ) : Prop :=
  ∀ e' ∈ plainEfforts P d, payoffPlain P d r e' ≤ payoffInvest P d r e

end ReservationPolicy



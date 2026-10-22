-- Prove2me | Definitions.Def_BidPriceControl_NonOptimal_CounterExample
-- name    : BidPriceControl_NonOptimal_CounterExample
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T12:15:10.994827+00:00
-- url     : https://prove2.me/theorems/0aabe336-06c2-4053-ae81-f36254742de9
-- title:
--   The two-leg, two-period instance of §3.1, Table 1: seat matrix, capacity (1,1), request laws
-- statement:
--   The instance of §3.1 and Table 1 has $m = 2$ legs and $n = 3$ itineraries: the **through** itinerary $A^0 = (1,1)$, using one seat on each leg, and the **local** itineraries $A^1 = (1,0)$ and $A^2 = (0,1)$. The initial capacity is $x = (1,1)$ and there are $k = 2$ periods to go. The request laws, indexed by time-to-go, are
--   $$F_2 = 0.4\,\delta_{(500,0,0)} + 0.3\,\delta_{(0,250,0)} + 0.3\,\delta_{(0,0,250)}, \qquad F_1 = 0.8\,\delta_{(500,0,0)} + 0.2\,\delta_{(0,0,0)}:$$
--   in period 2 (two periods to go) a through request with fare \$500 arrives with probability 0.4 and each local request with fare \$250 with probability 0.3; in period 1 (the last period) a through request with fare \$500 arrives with probability 0.8 and nothing with probability 0.2.
--
--   **Formalization Note.** Legs and itineraries are 0-indexed (the paper's legs 1, 2 are `0`, `1`). The probabilities are exact rationals as `ENNReal` weights of Dirac measures. The laws at every other time index are the no-arrival law $\delta_0$; only $F_1$ and $F_2$ enter the two-period problem. The fares are deterministic, which violates the continuity assumption of §1, as the paper notes (p. 1581).
-- source:
--   Talluri, van Ryzin, An Analysis of Bid-Price Controls for Network Revenue Management, Management Sci. 44(11), 1998, pp. 1581–1582, §3.1 and Table 1

import Mathlib
import Definitions.Def_BidPriceControl_NonOptimal_Model

namespace BidPriceControl.NonOptimal

open MeasureTheory

/-- The seat matrix of the counterexample of §3.1, Table 1 (pp. 1581–1582): two legs (rows
`0, 1` = the paper's legs 1, 2) and three itineraries (columns): the through itinerary
`A^0 = (1, 1)` and the two local itineraries `A^1 = (1, 0)`, `A^2 = (0, 1)`. -/
def ceA : Fin 2 → Fin 3 → ℕ := ![![1, 1, 0], ![1, 0, 1]]

/-- The initial capacity of §3.1: one unit of capacity on each leg, `x = (1, 1)`. -/
def ceX : Fin 2 → ℕ := ![1, 1]

/-- The request laws of Table 1 (p. 1581), indexed by time-to-go:
period 2 (two periods to go): a through request with fare $500 w.p. 0.4, a request for local
itinerary `(1 0)` with fare $250 w.p. 0.3, a request for local itinerary `(0 1)` with fare $250
w.p. 0.3; period 1 (the last period): a through request with fare $500 w.p. 0.8, no arrival
w.p. 0.2. The horizon has two periods; every other time index carries the no-arrival law. -/
noncomputable def ceLaw : ℕ → Measure (Fin 3 → ℝ)
  | 2 => (2 / 5 : ENNReal) • Measure.dirac ![500, 0, 0] +
         (3 / 10 : ENNReal) • Measure.dirac ![0, 250, 0] +
         (3 / 10 : ENNReal) • Measure.dirac ![0, 0, 250]
  | 1 => (4 / 5 : ENNReal) • Measure.dirac ![500, 0, 0] +
         (1 / 5 : ENNReal) • Measure.dirac ![0, 0, 0]
  | _ => Measure.dirac ![0, 0, 0]

end BidPriceControl.NonOptimal



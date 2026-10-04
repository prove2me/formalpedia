-- Prove2me | Definitions.Def_SeatInventory_Distinct_DemandModel
-- name    : SeatInventory_Distinct_DemandModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T05:47:52.559892+00:00
-- url     : https://prove2.me/theorems/ed832e27-c6e6-48b7-ab2b-ff2ff4841e68
-- title:
--   Requests, bookings, spill, expected revenue and EMSR of a distinct fare-class inventory
-- statement:
--   A single flight leg sells seats in several **fare classes**. In a **distinct** (non-nested) seat inventory, each class $i$ receives its own allocation of $S_i$ seats: once a seat is assigned to a class it may be booked only in that class or remain unsold. Class $i$ has average fare $f_i$ and receives a random number $r_i \in \{0,1,2,\dots\}$ of requests, with law $p_i$.
--
--   For one class with request law $p$ and $S$ seats, a request is booked while seats remain and is refused (spilled) otherwise, so bookings are $b = \min(r,S)$ and spill is $l = (r-S)^+$ (Eq. (5.3)). The definitions are
--
--   1. the **tail probability** $\bar P(S) = P[r \ge S]$ (Eq. (6.2)), the probability of selling $S$ or more seats;
--   2. the **expected bookings** $\bar b(S) = E[\min(r,S)] = \sum_{r\ge 0} p(r)\min(r,S)$ (Eq. (5.4));
--   3. the **expected spill** $\bar l(S) = E[(r-S)^+]$ (Eq. (5.5));
--   4. the **expected requests** $\bar r = E[r]$;
--   5. the **expected revenue** of the class, $\bar R(S) = f\cdot \bar b(S)$, and of the leg, $\bar R = \sum_i \bar R_i(S_i)$ (Eq. (5.9));
--   6. the **expected marginal seat revenue** of the $S$-th seat,
--   $$
--   \mathrm{EMSR}(S) = f\cdot \bar P(S) = f\cdot P[r\ge S] \qquad \text{(Eqs. (5.11), (6.1))}.
--   $$
--
--   These are the objects of Belobaba's static model for allocating a fixed capacity among distinct fare-class inventories; every theorem of the mission is stated in terms of them.
--
--   **Formalization Note** Requests are integer valued: the law of $r$ is a `PMF ℕ`. The thesis writes these quantities with continuous densities, but requires integer seat allocations (p. 103) and defines $\bar P(S) = P[r \ge S]$ in Eq. (6.2) and in the prose of Eq. (5.11); Eq. (5.2) writes $P[r > S]$, which agrees only for continuous demand. The integer reading with $\ge$ is the one under which the book's marginal-revenue identity (5.11) holds. Expected bookings are always finite (the summand is at most $S\,p(r)$). Expected spill and expected requests are series that Lean sets to $0$ when they diverge, so every theorem that uses them assumes a finite mean.
-- source:
--   Belobaba, Air Travel Demand and Airline Seat Inventory Management, MIT Flight Transportation Laboratory Report R87-7 (PhD thesis), 1987, pp. 102-105, Eqs. (5.1)-(5.5), (5.9), (5.11); p. 142, Eqs. (6.1)-(6.2)

import Mathlib

namespace SeatInventory.Distinct

/-- `P̄(S) = P[r ≥ S]`, the probability that the number of requests `r` of a fare class, with
law `p` on `ℕ`, is at least `S` (Belobaba 1987, Eq. (6.2), p. 142; the prose of Eq. (5.11),
p. 105: "the probability of selling `S` or more seats"). Requests are integer valued. -/
noncomputable def tailProb (p : PMF ℕ) (S : ℕ) : ℝ :=
  (p.toOuterMeasure (Set.Ici S)).toReal

/-- Expected bookings `b̄(S) = E[min(r, S)]` of a distinct fare-class inventory holding `S` seats
(Eqs. (5.3)–(5.4), p. 103): `r` requests are booked up to the `S` seats allocated. The summand is
bounded by `S · p(r)`, so the series always converges. -/
noncomputable def expectedBookings (p : PMF ℕ) (S : ℕ) : ℝ :=
  ∑' r : ℕ, (p r).toReal * ((min r S : ℕ) : ℝ)

/-- Expected spill `l̄(S) = E[(r − S)⁺]`, the expected number of refused requests
(Eqs. (5.3), (5.5), p. 103). `r - S` is truncated subtraction on `ℕ`, i.e. `(r − S)⁺`.
If `r` has infinite mean the series diverges and Lean's `tsum` returns `0`; every theorem using
this quantity assumes a finite mean. -/
noncomputable def expectedSpill (p : PMF ℕ) (S : ℕ) : ℝ :=
  ∑' r : ℕ, (p r).toReal * ((r - S : ℕ) : ℝ)

/-- Expected number of requests `r̄ = E[r]` (p. 103). Meaningful when the mean is finite; every
theorem using it assumes `Summable (fun r => (p r).toReal * r)`. -/
noncomputable def meanRequests (p : PMF ℕ) : ℝ :=
  ∑' r : ℕ, (p r).toReal * (r : ℝ)

/-- Expected revenue `R̄_i(S) = f_i · b̄_i(S)` of one fare class with average fare `f` and request
law `p`, holding `S` seats (Eq. (5.9), p. 105). -/
noncomputable def expectedRevenue (f : ℝ) (p : PMF ℕ) (S : ℕ) : ℝ :=
  f * expectedBookings p S

/-- Total expected revenue `R̄ = Σ_i R̄_i(S_i)` of a flight leg whose seats are split into
distinct (non-nested) inventories `S i`, one per fare class `i` (Eq. (5.9), p. 105);
`f i` is the average fare and `d i` the law of the requests of class `i`. -/
noncomputable def totalExpectedRevenue {ι : Type*} [Fintype ι] (f : ι → ℝ) (d : ι → PMF ℕ)
    (S : ι → ℕ) : ℝ :=
  ∑ i, expectedRevenue (f i) (d i) (S i)

/-- Expected marginal seat revenue of the `S`-th seat, `EMSR(S) = f · P̄(S) = f · P[r ≥ S]`
(Eq. (5.11), p. 105; Eqs. (6.1)–(6.2), p. 142); for `S ≥ 1` it is the `m_i(S)` of p. 90. -/
noncomputable def emsr (f : ℝ) (p : PMF ℕ) (S : ℕ) : ℝ :=
  f * tailProb p S

end SeatInventory.Distinct



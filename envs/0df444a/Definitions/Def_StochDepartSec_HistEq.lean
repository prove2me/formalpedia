-- Prove2me | Definitions.Def_StochDepartSec_HistEq
-- name    : StochDepartSec_HistEq
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:57:04.223054+00:00
-- url     : https://prove2.me/theorems/14590dfc-9af1-40ee-82ad-d2de0aca3a43
-- title:
--   Equality of histories until time $t$
-- statement:
--   Two outcomes $\omega,\omega'$ have the **same history until time $t$** if
--
--   1. they have the same seed;
--   2. the same candidates have arrived by $t$, and each of them has the same arrival time in both;
--   3. each candidate that has arrived by $t$ has departed by $t$ in both outcomes or in neither, and in the first case at the same time in both;
--   4. the candidates that have arrived by $t$ are in the same relative order in both.
--
--   This encodes the paper's history $h=(\vec a,\vec d,\vec r)$ at time $t$: arrival times, departure times in $[0,t]$ or "not yet departed", and relative ranks of the arrived candidates. Waiting times of candidates still present, future arrivals, and the comparison of arrived with unarrived candidates are not part of it.
--
--   **Formalization Note** A history is encoded as an equivalence relation on outcomes; a policy sees the history iff its decision is constant on equivalence classes. The history additionally contains the candidates' labels and the seed, which are independent of times and order. Departures at time $t$ itself belong to the history.
-- source:
--   Kesselheim, Psomas, Vardi, How to Hire Secretaries with Stochastic Departures, arXiv:1909.08660v1, §2, p.5 (histories)

import Mathlib
import Definitions.Def_StochDepartSec_Outcome
import Definitions.Def_StochDepartSec_dep

namespace StochDepartSec

/-- Two outcomes have the same history until time `t`: the same seed, the same candidates have
arrived by `t` with the same arrival times, each arrived candidate has departed by `t` in both or
in neither (and then at the same time), and the arrived candidates are in the same relative order.
Kesselheim, Psomas, Vardi, *How to Hire Secretaries with Stochastic Departures*, arXiv:1909.08660v1, §2, p.5: "A history is a triple h = (a, d, r) such that, for some k, a ∈ [0,1]^k is a vector of
arrival times, a_1 ≤ a_2 ≤ … ≤ a_k. d ∈ ([0,t] ∪ ⊥)^k is a vector of departure times (where ⊥
indicates the candidate has not departed by time t), and r are the relative ranks of the k
candidates. Note that the history cannot contain the realization of the random variable for the
time a candidate stays in the system if he is still there at time t."

**Formalization Note** A history is encoded as an equivalence relation on outcomes; a policy sees
the history iff its decision is constant on classes. Beyond the paper's triple the history also
contains the candidates' labels and the seed; both are independent of the times and of the order,
so they carry no information about the future (the seed is the policy's own randomness). Departures
at time `t` itself belong to the history (`d ∈ [0, t]`). -/
def HistEq {n : ℕ} (t : ℝ) (ω ω' : Outcome n) : Prop :=
  seed ω = seed ω' ∧
  (∀ i, arrival ω i ≤ t ↔ arrival ω' i ≤ t) ∧
  (∀ i, arrival ω i ≤ t →
    arrival ω i = arrival ω' i ∧ (dep ω i ≤ t ↔ dep ω' i ≤ t) ∧ (dep ω i ≤ t → dep ω i = dep ω' i)) ∧
  (∀ i j, arrival ω i ≤ t → arrival ω j ≤ t → (rank ω i < rank ω j ↔ rank ω' i < rank ω' j))

end StochDepartSec



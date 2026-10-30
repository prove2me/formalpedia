-- Prove2me | Definitions.Def_OnDemandRideHailing_CallNoCall_QueueStable
-- name    : OnDemandRideHailing_CallNoCall_QueueStable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:56:36.465987+00:00
-- url     : https://prove2.me/theorems/ea15d243-ad95-4027-8510-8c02329c042c
-- title:
--   Stability of a state-dependent M/M/k queue: both series of the waiting-time formula converge
-- statement:
--   Consider a single-queue birth–death system with arrival rate $\lambda$ and service rate $\mu_i>0$ when there are $i\ge1$ customers in the system. The queue is called **stable** when both series
--
--   $$
--   \sum_{i=0}^{\infty}\frac{\lambda^i}{\mu_1\mu_2\cdots\mu_i}
--   \qquad\text{and}\qquad
--   \sum_{i=1}^{\infty}\frac{i\,\lambda^{i-1}}{\mu_1\mu_2\cdots\mu_i}
--   $$
--
--   converge (the $i=0$ term of the first series is $1$, the empty product). By the proof of Theorem 1, Part 1 (p. 34), finiteness of the average waiting time is equivalent to the finiteness of these two series.
--
--   **Formalization Note** The rates are a sequence $\mu:\mathbb N\to\mathbb R$ whose index $0$ is unused. The second series is reindexed $i\mapsto i+1$ to avoid natural-number subtraction.
-- source:
--   Feng, Kong, Wang, We Are on the Way: Analysis of On-Demand Ride-Hailing Systems, SSRN 2960991, proof of Theorem 1, Part 1, p. 34

import Mathlib

namespace OnDemandRideHailing.CallNoCall

/-- **Stability of a state-dependent M/M/k queue: both series of the waiting-time formula converge.**
Feng, Kong, Wang, *We Are on the Way: Analysis of On-Demand Ride-Hailing Systems*, SSRN 2960991, proof of Theorem 1, Part 1, p. 34: "It is equivalent to show
`Σ_{i=1}^∞ iλ^{i−1}/(µ1µ2···µi)` and `Σ_{i=1}^∞ λ^i/(µ1µ2···µi)` are both finite".

`lam` is the Poisson arrival rate `λ` and `μ i` (for `i ≥ 1`) the service rate in state `i`
(`i` passengers in the system); `μ 0` is unused. The queue is *stable* when both series
`Σ_{i≥0} λ^i/(µ1⋯µi)` (the `i = 0` term is `1`, the empty product) and
`Σ_{i≥1} iλ^{i−1}/(µ1⋯µi)` converge.

**Formalization Note.** The second series is reindexed `i ↦ i + 1`, so its `i`-th term is
`(i+1)λ^i/(µ1⋯µ_{i+1})`; this avoids natural-number subtraction. Rates are meant to be positive
at every index `≥ 1`; with a zero rate Lean's `x / 0 = 0` would make the terms junk, and every
statement in this mission either uses the paper's positive rates (1), (3) or assumes positivity. -/
def QueueStable (lam : ℝ) (μ : ℕ → ℝ) : Prop :=
  Summable (fun i : ℕ => lam ^ i / ∏ j ∈ Finset.Icc 1 i, μ j) ∧
    Summable (fun i : ℕ => ((i : ℝ) + 1) * lam ^ i / ∏ j ∈ Finset.Icc 1 (i + 1), μ j)

end OnDemandRideHailing.CallNoCall



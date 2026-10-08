-- Prove2me | Definitions.Def_QueueingFundamentals_GM1_WaitingTime
-- name    : QueueingFundamentals_GM1_WaitingTime
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T09:51:54.563512+00:00
-- url     : https://prove2.me/theorems/b1a11dd8-5fca-40b7-9368-619ac5419130
-- title:
--   FCFS waiting-time CDFs seen by arrivals, $W_q(t)$ and $W(t)$
-- statement:
--   Consider a single exponential server with rate $\mu$ serving first come, first served, and let $q_n$ be the probability that an arriving customer finds $n$ customers in the system.
--
--   For $n \ge 1$ and $t$, let
--   $$
--   \Pr\{n \text{ completions in} \le t\} = \int_0^t \frac{\mu(\mu x)^{n-1}}{(n-1)!} e^{-\mu x}\,dx ,
--   $$
--   the Erlang type-$n$ CDF (the sum of $n$ independent exponential service times), and set it to $1$ for $n = 0$. Following §2.2.5 (p.65), the line-delay CDF of an arrival is
--   $$
--   W_q(t) = q_0 + \sum_{n\ge1} \Pr\{n \text{ completions in} \le t\}\, q_n ,
--   $$
--   because an arrival finding $n$ in the system enters service after $n$ completions (the residual service time of the customer in service is again exponential). The system-waiting-time CDF is
--   $$
--   W(t) = \sum_{n\ge0} \Pr\{n+1 \text{ completions in} \le t\}\, q_n ,
--   $$
--   since the arrival leaves after its own service as well.
--
--   These are the waiting-time distributions "as observed by customers arriving to the system" of Eqs. (5.62)–(5.63).
--
--   **Formalization Note** The CDFs are defined for any real $t$ and any sequence $q$; the theorems use them for $t \ge 0$ and a stationary probability vector $q$, for which the series converge.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.65 (§2.2.5, derivation of Eq. (2.28)) and p.263, Eq. (5.62)

import Mathlib

namespace QueueingFundamentals.GM1

/-- `Pr{n completions in ≤ t}` for exponential service at rate `μ` (§2.2.5, p.65): the Erlang
type-`n` CDF `∫_0^t μ(μx)^{n-1}/(n-1)! e^{-μx} dx` for `n ≥ 1`, and `1` for `n = 0` (no completion
is needed). -/
noncomputable def completionsCDF (mu : ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 1
  | m + 1, t => ∫ x in (0 : ℝ)..t,
      mu * (mu * x) ^ m / (Nat.factorial m : ℝ) * Real.exp (-mu * x)

/-- The FCFS line-delay CDF of an arriving customer (§2.2.5, p.65, with the arrival-point
probabilities `q_n`): `W_q(t) = q_0 + ∑_{n ≥ 1} Pr{n completions in ≤ t} q_n`. -/
noncomputable def lineDelayCDF (q : ℕ → ℝ) (mu t : ℝ) : ℝ :=
  ∑' n : ℕ, q n * completionsCDF mu n t

/-- The FCFS system-waiting-time CDF of an arriving customer: an arrival that finds `n` in the system
leaves after `n + 1` exponential service completions, so `W(t) = ∑_{n ≥ 0} Pr{n+1 completions in ≤ t} q_n`. -/
noncomputable def systemWaitCDF (q : ℕ → ℝ) (mu t : ℝ) : ℝ :=
  ∑' n : ℕ, q n * completionsCDF mu (n + 1) t

end QueueingFundamentals.GM1



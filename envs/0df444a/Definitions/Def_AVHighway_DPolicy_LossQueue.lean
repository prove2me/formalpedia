-- Prove2me | Definitions.Def_AVHighway_DPolicy_LossQueue
-- name    : AVHighway_DPolicy_LossQueue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:30.043982+00:00
-- url     : https://prove2.me/theorems/72f9f0a2-0543-4923-944f-728d3e0d8d76
-- title:
--   §3.1.1, §5 (12)–(13), pp. 7, 15 — the M/G_n/c/c loss queue: stationary law π_n, throughput θ, mean travel time W
-- statement:
--   The state-dependent loss queue $M/G_n/c/c$ used for a highway segment.
--
--   A segment of length $L>0$ holds at most $c$ vehicles (its **capacity**). Vehicles arrive according to a Poisson process with rate $\lambda$; a vehicle that finds $c$ vehicles on the segment is turned away. When $n$ vehicles are on the segment ($1 \le n \le c$) each of them travels at mean speed $V_n$, so the speeds form a sequence $V_1, V_2, \dots, V_c$.
--
--   1. **Stationary weights.** For $n \ge 0$,
--   $$w_n = \frac{(\lambda L)^n}{n!\,V_n V_{n-1}\cdots V_1},$$
--   with $w_0 = 1$ (empty product).
--
--   2. **Stationary law** (display (12), due to Cheah and Smith, 1994). For $0 \le n \le c$,
--   $$\pi_n = \frac{w_n}{\sum_{m=0}^{c} w_m}, \qquad\text{i.e.}\qquad \pi_n = \frac{(\lambda L)^n}{n!\,V_n\cdots V_1}\,\pi_0,\quad \pi_0 = \Bigl(1 + \sum_{n=1}^{c}\frac{(\lambda L)^n}{n!\,V_n\cdots V_1}\Bigr)^{-1}.$$
--
--   3. **Throughput** (effective arrival rate, by PASTA): $\theta = \lambda(1 - \pi_c)$.
--
--   4. **Mean travel time** (display (13), Little's law):
--   $$W = \frac{\sum_{n=1}^{c} n\,\pi_n}{\theta}.$$
--
--   These are the performance measures of every queue in the paper (the benchmark highway, and the AV and HV queues of the designated-lane policy).
--
--   **Formalization Note** The queue is represented by its closed-form stationary law (12), exactly as in the paper; no continuous-time Markov chain is constructed, and the platooning (MAP) layer of §3.1.2 that produces the speeds is not modelled: the speeds are an arbitrary real sequence $V : \mathbb N \to \mathbb R$, read at $n = 1, \dots, c$. Positivity and monotonicity of the speeds are hypotheses of the theorems, not part of the definitions. The rate is called `lam` because `λ` is a Lean keyword. Lean's convention $x/0 = 0$ makes $W = 0$ at $\lambda = 0$ (where $\theta = 0$); no statement of the mission uses that value. `stationary` is only meaningful for $0 \le n \le c$.
-- source:
--   Mirzaeian, Cho & Scheller-Wolf, A Queueing Model and Analysis for Autonomous Vehicles on Highways, SSRN 3278330 (version of May 5, 2020; Manag. Sci. doi:10.1287/mnsc.2020.3692), §3.1.1, p. 7; §5, displays (12)–(13), p. 15

import Mathlib

namespace AVHighway.DPolicy

/-- The unnormalised stationary weight of state `n` of the `M/G_n/c/c` queue, display (12), p. 15:
`(λL)^n / (n! V_n ⋯ V_1)`. At `n = 0` it is `1` (empty product, `0! = 1`), so the normaliser below is
`1 + Σ_{n=1}^c (λL)^n/(n! V_n ⋯ V_1)` exactly as in (12). -/
noncomputable def weight (L : ℝ) (V : ℕ → ℝ) (lam : ℝ) (n : ℕ) : ℝ :=
  (lam * L) ^ n / ((n.factorial : ℝ) * ∏ k ∈ Finset.Icc 1 n, V k)

/-- The stationary probability `π_n` of `n` vehicles on a segment of length `L` with capacity `cap`,
speeds `V_1, …, V_cap` and Poisson arrival rate `λ`, display (12), p. 15 (Cheah & Smith 1994):
`π_n = ((λL)^n / (n! V_n ⋯ V_1)) π_0`, `π_0 = (1 + Σ_{n=1}^{cap} (λL)^n / (n! V_n ⋯ V_1))^{-1}`.
Only `0 ≤ n ≤ cap` is meaningful. -/
noncomputable def stationary (L : ℝ) (V : ℕ → ℝ) (cap : ℕ) (lam : ℝ) (n : ℕ) : ℝ :=
  weight L V lam n / ∑ m ∈ Finset.range (cap + 1), weight L V lam m

/-- The throughput (effective arrival rate) `θ = λ(1 − π_cap)`, p. 15. -/
noncomputable def throughput (L : ℝ) (V : ℕ → ℝ) (cap : ℕ) (lam : ℝ) : ℝ :=
  lam * (1 - stationary L V cap lam cap)

/-- The mean travel time by Little's law, display (13), p. 15:
`W = (Σ_{n=1}^{cap} n π_n) / θ`. (At `λ = 0`, `θ = 0` and Lean's `x / 0 = 0` gives `W = 0`.) -/
noncomputable def meanTravelTime (L : ℝ) (V : ℕ → ℝ) (cap : ℕ) (lam : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 cap, (n : ℝ) * stationary L V cap lam n) / throughput L V cap lam

end AVHighway.DPolicy



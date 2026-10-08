-- Prove2me | Definitions.Def_HalfinWhitt81_Stationary_Basic
-- name    : HalfinWhitt81_Stationary_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:28:03.112872+00:00
-- url     : https://prove2.me/theorems/c06fc0b3-acd7-4d97-9434-5cc56289a524
-- title:
--   Probabilities and the scaled expectation of a law on {0, 1, 2, …}: P(Q ≤ x), P(Q ≥ x), P(Q = m), E g((Q − n)/√n)
-- statement:
--   Let $Q$ be a random variable with values in $\{0,1,2,\dots\}$ and probabilities $q_k = P(Q = k)$. This file names the four quantities of $Q$ that the limit theorems of Section 2 of Halfin and Whitt (1981) are written in.
--
--   1. For a real threshold $x$, $$P(Q \le x) = \sum_{k \ge 0,\ k \le x} q_k .$$
--   2. For a real threshold $x$, $$P(Q \ge x) = \sum_{k \ge 0,\ k \ge x} q_k .$$
--   3. For an integer $m$, $P(Q = m)$ is $q_m$ when $m \ge 0$ and $0$ when $m < 0$. With $m = [x]$, the greatest integer less than or equal to $x$, this is the paper's $P(Q = [x])$.
--   4. For $n \ge 1$ and a function $g:\mathbb R \to \mathbb R$, the expectation of $g(X)$ for the scaled variable $X = (Q - n)/\sqrt n$ of (2.13): $$E\,g\Big(\frac{Q-n}{\sqrt n}\Big) = \sum_{k \ge 0} q_k \, g\Big(\frac{k-n}{\sqrt n}\Big).$$
--
--   These are the probabilities $P(Q_n(\infty) \le \delta_n)$, $P(Q_n(\infty) \ge \delta_n)$, $P(Q_n(\infty) = [\delta_n])$ of Proposition 2 and the expectations $E\,g(X_n)$ through which weak convergence in Theorem 1 and the moments in Corollary 1 are stated.
--
--   **Formalization Note** All four are infinite sums (`tsum`) over $k \in \mathbb N$. They have their intended value whenever $q \ge 0$ is summable and, in item 4, $k \mapsto q_k\,g((k-n)/\sqrt n)$ is summable; this holds for a steady state of the M/M/n queue and bounded $g$. For unbounded $g$ (the moments of Corollary 1) the summability is part of the statement that uses it, never assumed. The function $P(Q = m)$ has at most one nonzero term.
-- source:
--   Halfin and Whitt, Heavy-Traffic Limits for Queues with Many Exponential Servers, Operations Research 29 (1981), p. 575, Section 2 ([x] before Proposition 2) and p. 576, (2.13)

import Mathlib

namespace HalfinWhitt81.Stationary

/-- `P(Q ≤ x)` for a random variable `Q` on `{0, 1, 2, …}` with probabilities `q k = P(Q = k)`:
the total mass of the states `k` with `k ≤ x` (a real threshold). -/
noncomputable def probLE (q : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, if (k : ℝ) ≤ x then q k else 0

/-- `P(Q ≥ x)` for a random variable `Q` on `{0, 1, 2, …}` with probabilities `q k = P(Q = k)`:
the total mass of the states `k` with `x ≤ k` (a real threshold). -/
noncomputable def probGE (q : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, if x ≤ (k : ℝ) then q k else 0

/-- `P(Q = m)` for an integer `m`, for a random variable `Q` on `{0, 1, 2, …}` with probabilities
`q k = P(Q = k)`; it is `q m` when `m ≥ 0` and `0` when `m < 0`. -/
noncomputable def probEqInt (q : ℕ → ℝ) (m : ℤ) : ℝ :=
  ∑' k : ℕ, if (k : ℤ) = m then q k else 0

/-- `E[g(X)]` for `X = (Q − n)/√n` (the scaling (2.13) of Halfin–Whitt with exponent `−1/2`),
where `Q` is a random variable on `{0, 1, 2, …}` with probabilities `q k = P(Q = k)`:
`∑_k q_k · g((k − n)/√n)`. -/
noncomputable def scaledExpect (q : ℕ → ℝ) (n : ℕ) (g : ℝ → ℝ) : ℝ :=
  ∑' k : ℕ, q k * g (((k : ℝ) - n) / Real.sqrt n)

end HalfinWhitt81.Stationary



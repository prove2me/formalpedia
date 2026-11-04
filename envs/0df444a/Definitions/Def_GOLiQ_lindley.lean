-- Prove2me | Definitions.Def_GOLiQ_lindley
-- name    : GOLiQ_lindley
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:50:16.938201+00:00
-- url     : https://prove2.me/theorems/f494251c-d8ca-4026-a123-923c21c5bfb9
-- title:
--   Lindley's recursion for waiting times and observed busy periods
-- statement:
--   Given an initial waiting time $w_0$, an initial observed busy period $x_0$, service times $s_n$ and interarrival times $\tau_n$ ($n\ge1$), define $(W_0,X_0)=(w_0,x_0)$ and, for $n\ge1$,
--   $$W_n=(W_{n-1}+s_n-\tau_n)^+,\qquad X_n=(X_{n-1}+\tau_n)\,\mathbf 1\{W_n>0\}.$$
--   $W_n$ is the waiting time of customer $n$ and $X_n$ the time the server has been busy when customer $n$ arrives ($0$ if the server is idle).
--
--   The inputs may vary with $n$, so the same recursion describes the queue with time-varying rates (Lemma 3), the synchronous coupling of two queues (Lemmas 2 and 6), and the stationary sequence of Corollary 1.
-- source:
--   Chen, Liu, Hong, An Online Learning Approach to Dynamic Pricing and Capacity Sizing in Service Systems, arXiv:2009.02911v3, §3.3, recursions (6)–(7), p.16; synchronous coupling, p.24; Lemma 3, p.25

import Mathlib

namespace GOLiQ

/-- **Lindley's recursion for waiting times and the observed busy period** with time-varying inputs
(Chen, Liu, Hong, arXiv:2009.02911v3, recursions (6)–(7), p.16; the synchronous coupling of p.24;
Lemma 3, p.25).

Given an initial waiting time `w₀`, an initial observed busy period `x₀`, service times `s n` and
interarrival times `τ n` (`n ≥ 1`), the value at `n` is the pair `(Wₙ, Xₙ)` with
`(W₀, X₀) = (w₀, x₀)` and, for `n ≥ 1`,

`Wₙ = (Wₙ₋₁ + sₙ − τₙ)⁺`,    `Xₙ = (Xₙ₋₁ + τₙ) · 1{Wₙ > 0}`.

`Wₙ` is the waiting time of customer `n`; `sₙ` is the service time of customer `n − 1` and `τₙ` the
time between the arrivals of customers `n − 1` and `n`. `Xₙ` is the length of time the server has
been busy when customer `n` arrives (`0` if the customer finds the server idle). -/
noncomputable def lindley (w₀ x₀ : ℝ) (s τ : ℕ → ℝ) : ℕ → ℝ × ℝ
  | 0 => (w₀, x₀)
  | n + 1 =>
      let w := max ((lindley w₀ x₀ s τ n).1 + s (n + 1) - τ (n + 1)) 0
      (w, if 0 < w then (lindley w₀ x₀ s τ n).2 + τ (n + 1) else 0)

end GOLiQ



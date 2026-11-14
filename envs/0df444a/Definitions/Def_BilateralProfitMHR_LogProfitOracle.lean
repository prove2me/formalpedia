-- Prove2me | Definitions.Def_BilateralProfitMHR_LogProfitOracle
-- name    : BilateralProfitMHR_LogProfitOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-13T19:18:30.392126+00:00
-- url     : https://prove2.me/theorems/cb0bbcc0-d42f-46d8-9e65-b22439627d31
-- title:
--   Equation (32) — the harmonic numbers $H_m$, the law $\mathrm{Geom}(Q)$ and the one-bit estimator $Z=H_{N-1}-\log(q-p)$
-- statement:
--   For $m\ge1$ let $H_m=\sum_{k=1}^m 1/k$, and set $H_0=0$. For $Q\in(0,1]$, $\mathrm{Geom}(Q)$ is the law of the number of trials up to and including the first success,
--   $$\Pr(N=k)=(1-Q)^{k-1}Q\qquad(k\ge1).$$
--
--   To estimate the loss $L(p,q)=-\log\mu(p,q)$ from trade bits, the algorithm posts the query $x=(p,q)$ until the first trade. With fresh i.i.d. valuations, the number $N$ of rounds used is $\mathrm{Geom}(P(p,q))$, where $P(p,q)$ is the trade probability, and the algorithm reports
--   $$Z=H_{N-1}-\log(q-p).\tag{32}$$
--   This file defines the law of $Z$ at each query, which answers the queries of the convex bandit routine in Lemma 5.6.
--
--   **Formalization Note** $\mathrm{Geom}(Q)$ is a measure on the natural numbers carried by $\{1,2,\dots\}$; $H_{N-1}$ uses truncated subtraction, which matters only at $N=0$, an event of probability zero.
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), §5.4, Equation (32), p.34 (PDF 36); Claim 5.5, p.35 (PDF 37)

import Mathlib
import Definitions.Def_BilateralProfit_Model

namespace BilateralProfitMHR

open MeasureTheory BilateralProfit

/-! # The one-bit log-profit oracle (Equation (32))

Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256 e91e8127…), §5.4, p.34 (PDF 36):
"For `m ≥ 1`, let `H_m = ∑_{k=1}^m 1/k`, and set `H_0 = 0`. … Let `N` be the number of rounds
used, then `Z = H_{N−1} − log(q − p)` (32)". `Geom(Q)` is the number of trials up to and
including the first success: `P(N = k) = (1 − Q)^{k−1} Q` for `k ≥ 1`.

**Formalization Note.** `Geom(Q)` is a measure on `ℕ` carried by `{1, 2, …}` (a probability
measure for `Q ∈ (0, 1]`). `H_{N−1}` uses natural subtraction; `N = 0` has probability zero.
The law of the observation of a query `x = (p, q)` is the law of `Z` when the waiting time `N`
is geometric with success probability the trade probability `P(p, q)` (posting `x` until the
first trade, with fresh i.i.d. valuations). Logarithms are natural. -/

/-- The harmonic number `H_m = ∑_{k=1}^m 1/k`, `H_0 = 0`. -/
noncomputable def harm (m : ℕ) : ℝ := ∑ k ∈ Finset.range m, 1 / ((k : ℝ) + 1)

/-- The geometric law `Geom(Q)` on `{1, 2, …}`: `P(N = k + 1) = (1 − Q)^k Q`. -/
noncomputable def geomLaw (Q : ℝ) : Measure ℕ :=
  Measure.sum fun k : ℕ => ENNReal.ofReal ((1 - Q) ^ k * Q) • Measure.dirac (k + 1)

/-- The law of the estimator `Z = H_{N−1} − log(q − p)` of Equation (32) at the query
`x = (p, q)`, with `N ∼ Geom(P(p, q))` for the trade probability `P` of the valuation law `D`. -/
noncomputable def oracleLaw (D : Measure (ℝ × ℝ)) (x : ℝ × ℝ) : Measure ℝ :=
  (geomLaw (Ptrade D x)).map fun N : ℕ => harm (N - 1) - Real.log (x.2 - x.1)

end BilateralProfitMHR



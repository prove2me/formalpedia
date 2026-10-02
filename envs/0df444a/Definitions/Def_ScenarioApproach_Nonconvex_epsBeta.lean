-- Prove2me | Definitions.Def_ScenarioApproach_Nonconvex_epsBeta
-- name    : ScenarioApproach_Nonconvex_epsBeta
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T18:41:38.805976+00:00
-- url     : https://prove2.me/theorems/b9562abe-4244-4cab-8b54-34b2c2a09667
-- title:
--   Eq. (8.16) — the violation level ε(k) for confidence β
-- statement:
--   Fix a sample size $N$ and a confidence parameter $\beta\in[0,1]$. For $k=0,1,\dots,N$ define
--
--   $$
--   \epsilon(k)=\begin{cases}1 & \text{if } k=N,\\[2pt] 1-\sqrt[N-k]{\dfrac{\beta}{N\binom{N}{k}}} & \text{otherwise.}\end{cases}
--   $$
--
--   This is the level function that, inserted in the bound (8.15), makes its right-hand side equal to $\beta$: the violation of the solution of a nonconvex scenario program with a support set of cardinality $k$ exceeds $\epsilon(k)$ with probability at most $\beta$.
--
--   **Formalization Note** The $(N-k)$-th root is `Real.rpow` with exponent `1 / (N - k)`, where `N - k` is natural-number subtraction cast to ℝ; for $k<N$ it is the positive integer $N-k$, and the base $\beta/(N\binom Nk)$ is nonnegative for $\beta\ge0$, so this is the real root. The definition is total in $k$; values at $k>N$ are never used.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 105, Eq. (8.16)

import Mathlib

namespace ScenarioApproach.Nonconvex

/-- Eq. (8.16). For a sample size `N` and a confidence parameter `β`,
`ε(k) = 1` if `k = N`, and `ε(k) = 1 − (β / (N · (N choose k)))^{1/(N−k)}` otherwise
(the real `(N−k)`-th root). Only the values at `k = 0, …, N` are used. -/
noncomputable def epsBeta (N : ℕ) (β : ℝ) (k : ℕ) : ℝ :=
  if k = N then 1
  else 1 - (β / ((N : ℝ) * (N.choose k : ℝ))) ^ ((1 : ℝ) / ((N - k : ℕ) : ℝ))

end ScenarioApproach.Nonconvex



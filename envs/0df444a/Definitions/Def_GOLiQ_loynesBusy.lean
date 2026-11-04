-- Prove2me | Definitions.Def_GOLiQ_loynesBusy
-- name    : GOLiQ_loynesBusy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:50:23.990768+00:00
-- url     : https://prove2.me/theorems/ba10ae89-5b52-4ab3-92e6-60df5c4dcaea
-- title:
--   Stationary observed busy period in Loynes' construction
-- statement:
--   With the backward partial sums $S_n=\sum_{j=1}^n(s_j-\tau_j)$, customer $-n$ found the server idle exactly when $S_m\le S_n$ for all $m\ge n$. Let $\nu$ be the least such $n\ge0$. The server has been busy since the arrival of customer $-\nu$, so the busy time observed by customer $0$ is
--   $$X_\infty=\sum_{j=1}^{\nu}\tau_j ,$$
--   and $X_\infty=0$ when customer $0$ finds the server idle. This is the stationary limit of the recursion for $X_n$.
--
--   **Formalization Note** If no such $\nu$ exists (probability $0$ for a stable queue), $\nu$ is the junk value $0$.
-- source:
--   Chen, Liu, Hong, An Online Learning Approach to Dynamic Pricing and Capacity Sizing in Service Systems, arXiv:2009.02911v3, Lemma 5, p.30 ($X_\infty$); Lemma 6, p.65

import Mathlib

namespace GOLiQ

/-- **The stationary observed busy period** in Loynes' construction (Chen, Liu, Hong,
arXiv:2009.02911v3, `X∞(µ, p)` of Lemma 5, p.30, and Lemma 6, p.65).

With the backward partial sums `Sₙ = Σ_{j=1}^n (sⱼ − τⱼ)` of `loynesWait`, customer `−n` found the
server idle exactly when `Sₘ ≤ Sₙ` for every `m ≥ n`. Let `ν` be the least such `n ≥ 0`; the server
has then been busy since the arrival of customer `−ν`, and the busy time observed by customer `0` is

`X∞ = Σ_{j=1}^{ν} τⱼ`.

In particular `X∞ = 0` when customer `0` finds the server idle (`ν = 0`). This is the `n → ∞` limit
of recursion (7) in the stationary queue.

**Formalization Note.** If no such `ν` exists (an event of probability `0` for a stable queue),
`ν` is the junk value `0`. -/
noncomputable def loynesBusy (s τ : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1
      (sInf {n : ℕ | ∀ m, n ≤ m →
        ∑ j ∈ Finset.Icc 1 m, (s j - τ j) ≤ ∑ j ∈ Finset.Icc 1 n, (s j - τ j)}),
    τ j

end GOLiQ



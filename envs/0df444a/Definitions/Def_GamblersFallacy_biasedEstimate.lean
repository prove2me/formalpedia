-- Prove2me | Definitions.Def_GamblersFallacy_biasedEstimate
-- name    : GamblersFallacy_biasedEstimate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:15.191997+00:00
-- url     : https://prove2.me/theorems/f08819e6-e36b-4431-9ece-10741388f212
-- title:
--   Demand arrivals, the empirical proportion $\hat p_j(n)$ and the biased estimate $p_j(n)=\mathbb E[\hat p_j(n)]$
-- statement:
--   A demand arrives at time position $0$ by assumption. In each of the periods $1,\dots,n$ a demand arrives independently with probability $p$; write $q=1-p$ and $B(t)\in\{0,1\}$ for the indicator of an arrival at position $t\in\{0,1,\dots,n\}$, so $B(0)=1$.
--
--   For a gap length $j\ge1$, the **empirical proportion** $\hat p_j(n)$ is the fraction of arrivals at positions $0,\dots,n-1$ whose next arrival comes exactly $j$ periods later, at a position not beyond $n$:
--   $$\hat p_j(n)=\frac{\#\{t\in\{0,\dots,n-1\}: B(t)=1,\ B(t+1)=\dots=B(t+j-1)=0,\ B(t+j)=1,\ t+j\le n\}}{\#\{t\in\{0,\dots,n-1\}: B(t)=1\}}.$$
--   For $j=1$ this is $\hat p_1(n)=\sum_{i=0}^{n-1}B(i)G(i)\big/\sum_{i=0}^{n-1}B(i)$, with $G(i)$ the indicator of arrivals at both $i$ and $i+1$. For general $j$ it is the random variable inside the expectation (1): the denominator is the number $\tau+1$ of arrivals up to period $n-1$, and the last arrival is counted exactly when it sits at $n-j$ and the next arrival is at $n$.
--
--   The **biased estimate** is the expectation
--   $$p_j(n)=\mathbb E\big[\hat p_j(n)\big],$$
--   and $p_1(n)$ is the case $j=1$. The relative bias of the paper is $(p-p_1(n))/p$.
--
--   These are the objects of Theorem 2 and Proposition 2: the finite-horizon estimate of the inter-arrival distribution that a planner reads off an observed demand history.
--
--   **Formalization Note** A path of the periods $1,\dots,n$ is `ω : Fin n → Bool`; `arrival ω t` is $B(t)$ (true at $t=0$, false beyond $n$, where it is never read). The path weight is $\prod_k(p\text{ if }\omega_k\text{ else }1-p)$ and the expectation is the finite weighted sum over the $2^n$ paths. The denominator is at least $1$ for $n\ge1$ because $B(0)=1$; at $n=0$ Lean returns $0/0=0$, a case the paper does not consider. The estimate is not defined by the closed form of Theorem 2.
-- source:
--   Bi–He–Teo, Taming the Long Tail, MSOM (2023), doi:10.1287/msom.2023.1217, §3.1, p.10 (B_n(t), G_n(t), B_n(0) = 1, p̂₁(n)); (1), p.11 (p_j(n)); §3.2, p.13 (initial arrival at time 0, i.i.d. arrivals with probability p); Table EC.1, p.ec1

import Mathlib

namespace GamblersFallacy

/-- **Demand arrivals at the positions `0, 1, …, n`.**
S. Bi, L. He, C.-P. Teo, *Taming the Long Tail: The Gambler's Fallacy in Intermittent Demand
Management*, MSOM (2023), doi:10.1287/msom.2023.1217, §3.1, p.10 ("Let B_n(t) denote the
indicator of the event that "1" is generated at the t-th position. … Note that B_n(0) = 1 since
we start at the initial state "1"") and §3.2, p.13 ("we assume an initial demand arrival at
time 0, which triggers the inter-arrival process").

`arrival ω t` is `B_n(t)`: a demand arrives at position `0` by assumption, at position
`1 ≤ t ≤ n` exactly when `ω ⟨t - 1, _⟩ = true`, and never beyond `n`.

**Formalization Note.** A sample path of the `n` random periods `1, …, n` is `ω : Fin n → Bool`
(entry `k` is the period `k + 1`). The value `false` beyond `n` is never read by `empiricalGap`,
which only looks at positions `t + j ≤ n`. -/
def arrival {n : ℕ} (ω : Fin n → Bool) (t : ℕ) : Bool :=
  if h0 : t = 0 then true else if h : t ≤ n then ω ⟨t - 1, by omega⟩ else false

/-- **The i.i.d. Bernoulli(`p`) weight of a sample path** (§3.2, p.13: "the probability of a
demand arriving in each time period is p", independently).

`pathWeight p ω = ∏_k (p if ω k else 1 - p)`, the probability of the path `ω` when the demands
at the periods `1, …, n` arrive independently with probability `p` each.

**Formalization Note.** For `p ∈ [0, 1]` these weights are the i.i.d. Bernoulli(`p`) law on
`Fin n → Bool`; expectations are written as finite weighted sums over the `2ⁿ` paths. -/
def pathWeight {n : ℕ} (p : ℝ) (ω : Fin n → Bool) : ℝ :=
  ∏ k, if ω k then p else 1 - p

/-- **A gap of length `j` opening at position `t`**: an arrival at `t`, no arrival at
`t + 1, …, t + j - 1`, and an arrival at `t + j ≤ n` (the transition `{1, 0¹, …, 0^{j-1}, 1}`
of Table EC.1, p.ec1). -/
def gapAt {n : ℕ} (ω : Fin n → Bool) (j t : ℕ) : Bool :=
  arrival ω t && decide (t + j ≤ n) && arrival ω (t + j) &&
    decide (∀ k ∈ Finset.Ioo t (t + j), arrival ω k = false)

/-- **The empirical proportion `p̂_j(n)`** (§3.1, p.10 for `j = 1`; (1), p.11 for general `j`;
Table EC.1, p.ec1: "the empirical proportion of transition {1, 0₁, …, 0_{j−1}, 1} in n-sample
0-1 sequence").

`empiricalGap n j ω` is the number of positions `t ∈ {0, …, n − 1}` that open a gap of length
`j` closing at a position `≤ n`, divided by the number of arrivals at the positions
`0, …, n − 1`. For `j = 1` this is the paper's `p̂₁(n) = Σ_{i=0}^{n−1} B_n(i) G_n(i) /
Σ_{i=0}^{n−1} B_n(i)` (p.10). For general `j` it is the random variable inside the expectation
(1): with arrivals at `0 = S₀ < S₁ < ⋯ < S_τ ≤ n − 1`, the denominator is `τ + 1`, the gaps
`Z₁, …, Z_τ` close at positions `≤ n − 1`, and the last arrival `S_τ` is counted exactly when
`S_τ = n − j` and the next arrival is at `n`.

**Formalization Note.** The denominator is at least `1` whenever `n ≥ 1`, because position `0`
always carries an arrival. At `n = 0` (no horizon) Lean's `0 / 0 = 0` is the value; the paper
does not consider this case and no theorem uses it. -/
noncomputable def empiricalGap (n j : ℕ) (ω : Fin n → Bool) : ℝ :=
  (((Finset.range n).filter fun t => gapAt ω j t = true).card : ℝ) /
    (((Finset.range n).filter fun t => arrival ω t = true).card : ℝ)

/-- **The biased estimate `p_j(n) := E[p̂_j(n)]`** ((1), p.11; Table EC.1, p.ec1), the
expectation of the empirical proportion `p̂_j(n)` when demands arrive independently with
probability `p` in each of the periods `1, …, n`. The paper's `p₁(n)` is `biasedEstimate n 1 p`.

**Formalization Note.** The expectation is the finite weighted sum
`Σ_ω pathWeight p ω · p̂_j(n)(ω)` over the `2ⁿ` paths `ω : Fin n → Bool`. As a function of `p`
it is a polynomial; it is **not** defined by the closed form of Theorem 2. -/
noncomputable def biasedEstimate (n j : ℕ) (p : ℝ) : ℝ :=
  ∑ ω : Fin n → Bool, pathWeight p ω * empiricalGap n j ω

end GamblersFallacy



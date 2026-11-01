-- Prove2me | Definitions.Def_GreedyReusableNet_ProblemInstance
-- name    : GreedyReusableNet_ProblemInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:33:49.846982+00:00
-- url     : https://prove2.me/theorems/21a6d459-d13e-4f41-92dc-7829bfc59c7a
-- title:
--   Problem instance $\mathcal I=\{\{\mathscr A_t\}_t,\{\mathbb P_t\}_t,\{r_t\}_t,\{F_i\}_i\}$
-- statement:
--   A **problem instance** consists of the data of every period $t$ (bundles, action sets, activation law, rewards) and, for every arm $i$ and count $n\in\mathbb N$, a **blocking-time distribution** $F_i(\cdot\,;n)$ on $\mathbb N$. When arm $i$ is activated in period $t$ after $n$ earlier activations, a blocking time $b\sim F_i(\cdot\,;n)$ is drawn and the arm cannot be used during the periods $(t,t+b]$.
--
--   **Formalization Note** Periods are $0$-based: the paper's $t=1,\dots,T$ are $t=0,\dots,T-1$, and only periods $t<T$ are ever read. Blocking times take values in $\mathbb N$, so $b=0$ (no blocking) is allowed, as on p.11 of the paper and in its examples with $F_i(x;n)=\mathbb 1\{x\ge0\}$. The blocking law depends on the arm and its count, not on $t$.
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, §2.3, p.15; Algorithm 1, pp.8–9; Blocking Time, p.11

import Mathlib
import Definitions.Def_GreedyReusableNet_PeriodData

namespace GreedyReusableNet

/-- **A problem instance** `𝓘 = {{𝒜_t}_t, {ℙ_t}_t, {r_t}_t, {F_i}_i}` (Simchi-Levi, Zheng & Zhu,
SSRN 3981123, §2.3, p.15; Algorithm 1, pp.8–9; §2.1, p.11).

`period t` is the data revealed in period `t` and `block i n` is the distribution `F_i(·; n)` of
the time `b_{t,i}` for which arm `i` is blocked after its activation, when it has been activated
`n` times before.

**Formalization Note**
* Periods are 0-based: the paper's `t = 1, …, T` is `t = 0, …, T - 1`; only `period t` with
  `t < T` is ever used.
* The times `b_{t,i}` take values in `ℕ` (the paper writes `b_{t,i} ∈ ℤ₊₊` but in the same paragraph
  allows `b_{t,i} = 0`, "arm i is not blocked", and its examples use `F_i(x; n) = 𝟙{x ≥ 0}`); an
  arm activated at period `t` with blocking time `b` is blocked during the periods `t + 1, …, t + b`,
  i.e. during `(t, t + b]`.
* `F_i` depends on the arm and its own count only, not on `t` (Algorithm 1: "the blocking time
  distribution `F_i(·; n^π_{t,i})` for each arm i"). -/
structure ProblemInstance (N : ℕ) where
  /-- the data `(𝓑_t, 𝒜_t, activation law, r_t)` of period `t` -/
  period : ℕ → PeriodData N
  /-- the blocking-time distribution `F_i(·; n)` of arm `i` at count `n` -/
  block : Fin N → ℕ → PMF ℕ

end GreedyReusableNet



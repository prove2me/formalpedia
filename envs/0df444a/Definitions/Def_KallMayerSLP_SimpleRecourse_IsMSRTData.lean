-- Prove2me | Definitions.Def_KallMayerSLP_SimpleRecourse_IsMSRTData
-- name    : KallMayerSLP_SimpleRecourse_IsMSRTData
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:12:24.980523+00:00
-- url     : https://prove2.me/theorems/ea573579-0f4b-4c6a-b989-b09c35e9abd1
-- title:
--   Admissible constants of a multiple simple recourse type function
-- statement:
--   Real constants $\{\alpha_k,\beta_k,u_k,l_k;\ k=0,\dots,K-1\}$ are admissible for a multiple simple recourse type function if
--
--   1. $\alpha_0+\beta_0\ge 0$, and $\alpha_k\ge0$, $\beta_k\ge0$ for $k=1,\dots,K-1$;
--   2. $\sum_{k=0}^{K-1}(\alpha_k+\beta_k)>0$;
--   3. $u_0=0<u_1<\dots<u_{K-1}$ and $l_0=0<l_1<\dots<l_{K-1}$.
--
--   The $u_k$ and $l_k$ are the breakpoints of the surplus and shortage costs, and $\alpha_k$, $\beta_k$ are the increments of the marginal costs. Only the combined weight $\alpha_0+\beta_0$ of the first piece has a sign condition.
--
--   **Formalization Note** Index base $0$ as in the book. $K\ge1$ follows from condition 2. The chains in 3 are $u_0=0$ plus strict monotonicity of $k\mapsto u_k$, and likewise for $l$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Definition 2.4, p.237 (PDF 246)

import Mathlib

namespace KallMayerSLP.SimpleRecourse

/-- **The constants of a multiple simple recourse type function, Definition 2.4.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, Definition 2.4, p.237 (PDF 246):
real constants `{α_k, β_k, u_k, l_k; k = 0, …, K − 1}` such that `α₀ + β₀ ≥ 0` and
`α_k ≥ 0, β_k ≥ 0` for `k = 1, …, K − 1` with `Σ_{k=0}^{K−1} (α_k + β_k) > 0`,
`u₀ = 0 < u₁ < ⋯ < u_{K−1}`, `l₀ = 0 < l₁ < ⋯ < l_{K−1}`.

**Formalization Note.** Index base `0`, as in the book: `Fin K` is `{0, …, K − 1}` and `k.val = 0`
picks `k = 0`. `K ≥ 1` is not a separate field: it follows from `sum_pos` (an empty sum is `0`).
The chains `u₀ = 0 < u₁ < ⋯` are `u_zero` plus `StrictMono u`; likewise for `l`. `α₀` and `β₀`
may be negative individually. -/
structure IsMSRTData (K : ℕ) (α β u l : Fin K → ℝ) : Prop where
  nonneg_zero : ∀ k : Fin K, k.val = 0 → 0 ≤ α k + β k
  alpha_nonneg : ∀ k : Fin K, k.val ≠ 0 → 0 ≤ α k
  beta_nonneg : ∀ k : Fin K, k.val ≠ 0 → 0 ≤ β k
  sum_pos : 0 < ∑ k, (α k + β k)
  u_zero : ∀ k : Fin K, k.val = 0 → u k = 0
  u_strictMono : StrictMono u
  l_zero : ∀ k : Fin K, k.val = 0 → l k = 0
  l_strictMono : StrictMono l

end KallMayerSLP.SimpleRecourse



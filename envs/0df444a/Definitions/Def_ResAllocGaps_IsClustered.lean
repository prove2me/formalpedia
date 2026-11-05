-- Prove2me | Definitions.Def_ResAllocGaps_IsClustered
-- name    : ResAllocGaps_IsClustered
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:30:09.615816+00:00
-- url     : https://prove2.me/theorems/5ff2d9f6-f7e0-4f50-ae67-574ec61306f6
-- title:
--   Definition 1: $(\beta,\varepsilon_0,\delta)$-clustered distributions
-- statement:
--   Fix $\beta\in[0,\infty)$, $\varepsilon_0\in(0,1]$ and $\delta\in[0,1]$. A distribution $F$ is **$(\beta,\varepsilon_0,\delta)$-clustered** if there are $n\in\mathbb N\cup\{0\}$ and gap quantiles $q^\star_0=0<q^\star_1<\dots<q^\star_n<q^\star_{n+1}=1$ such that
--
--   1. (cluster "density") for every $i\in[n+1]$ and all $q,\tilde q\in(q^\star_{i-1},q^\star_i]$,
--   $$|F^{-1}(q)-F^{-1}(\tilde q)|\le C\,|q-\tilde q|^{1/(\beta+1)}+\delta$$
--   for some constant $C<\infty$;
--   2. (cluster size) $q^\star_i-q^\star_{i-1}\ge\varepsilon_0$ for every $i\in[n+1]$.
--
--   The class $\mathscr F_{\beta,\varepsilon_0}$ is the case $\delta=0$. For $\delta=0$ condition 1 says that $F^{-1}$ is $1/(\beta+1)$-Hölder on each quantile interval of a cluster; $\beta$ measures how thin the mass is near the edges of the gaps.
--
--   **Formalization Note** The gap quantiles are a strictly increasing map $q:\{0,\dots,n+1\}\to\mathbb R$ with $q_0=0$, $q_{n+1}=1$; one constant $C$ serves all clusters (equivalent, as there are finitely many). The parameter ranges are part of the predicate. It does not by itself require $F$ to be a probability law on $[0,1]$; the statements that use it add that.
-- source:
--   O. Besbes, Y. Kanoria and A. Kumar, Dynamic Resource Allocation: Algorithmic Design Principles and Spectrum of Achievable Performances, arXiv:2205.09078v2 (6 Oct 2023), https://arxiv.org/abs/2205.09078v2, §3.1, p.11, Definition 1

import Mathlib
import Definitions.Def_ResAllocGaps_quantile

open MeasureTheory

namespace ResAllocGaps

/-- **Definition 1 ((β, ε₀, δ)-clustered distributions)**, Besbes, Kanoria & Kumar,
arXiv:2205.09078v2, §3.1, p.11. Fix `β ∈ [0, ∞)`, `ε₀ ∈ (0, 1]` and `δ ∈ [0, 1]`. A distribution
`F` is `(β, ε₀, δ)`-clustered if there exist `n ∈ ℕ ∪ {0}` and gap quantiles
`q⋆₀ = 0 < q⋆₁ < ⋯ < q⋆ₙ < q⋆ₙ₊₁ = 1` such that
(a) for every `i ∈ [n + 1]` and all `q, q̃ ∈ (q⋆ᵢ₋₁, q⋆ᵢ]`,
`|F⁻¹(q) − F⁻¹(q̃)| ≤ C |q − q̃|^{1/(β+1)} + δ` for some constant `C < ∞`, and
(b) `q⋆ᵢ − q⋆ᵢ₋₁ ≥ ε₀` for every `i ∈ [n + 1]`.
The class `𝓕_{β,ε₀}` of the paper is `IsClustered μ β ε₀ 0`.

**Formalization Note.** The gap quantiles are `q : Fin (n + 2) → ℝ`, strictly increasing, with
`q 0 = 0` and `q (Fin.last (n + 1)) = 1`; cluster `i ∈ [n + 1]` of the paper is the index
`i : Fin (n + 1)` with quantile interval `(q i.castSucc, q i.succ]`. One constant `C` serves all
clusters (equivalent, as there are finitely many clusters). The parameter ranges fixed in the
first sentence of the definition are conjuncts. `F⁻¹` is `quantile μ` and is evaluated only on
`(0, 1]`. The power is `Real.rpow` of `|q − q̃| ≥ 0`. The predicate does not itself require `μ` to
be a probability measure supported on `[0, 1]`; the statements that use it add those conditions. -/
def IsClustered (μ : Measure ℝ) (β ε₀ δ : ℝ) : Prop :=
  0 ≤ β ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧ 0 ≤ δ ∧ δ ≤ 1 ∧
    ∃ n : ℕ, ∃ q : Fin (n + 2) → ℝ, StrictMono q ∧ q 0 = 0 ∧ q (Fin.last (n + 1)) = 1 ∧
      ∃ C : ℝ, ∀ i : Fin (n + 1),
        (∀ x ∈ Set.Ioc (q i.castSucc) (q i.succ), ∀ y ∈ Set.Ioc (q i.castSucc) (q i.succ),
          |quantile μ x - quantile μ y| ≤ C * |x - y| ^ (1 / (β + 1)) + δ) ∧
        ε₀ ≤ q i.succ - q i.castSucc

end ResAllocGaps



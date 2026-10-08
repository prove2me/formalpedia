-- Prove2me | Definitions.Def_GenEmpLik_Consistency_IsGlivenkoCantelli
-- name    : GenEmpLik_Consistency_IsGlivenkoCantelli
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T08:53:15.27593+00:00
-- url     : https://prove2.me/theorems/bb7463d9-b80c-4712-a8f8-1cff6bdc16a3
-- title:
--   Definition 2 — Glivenko–Cantelli class
-- statement:
--   Let $\xi_1,\xi_2,\dots$ be random elements of $\Xi$ on a probability space, with common law $P_0$, and let $\widehat P_n$ be the empirical distribution of $\xi_1,\dots,\xi_n$. A collection $\mathcal H$ of functions $h:\Xi\to\mathbb R$ is **Glivenko–Cantelli** if
--
--   $$
--   \sup_{h\in\mathcal H}\big|E_{\widehat P_n}[h]-E_{P_0}[h]\big|\ \xrightarrow{\ \text{a.s.}^*\ }\ 0,
--   $$
--
--   that is, the strong law of large numbers holds uniformly over $\mathcal H$. It is the uniform convergence hypothesis of Theorem 7.
--
--   **Formalization Note** The samples are indexed from $0$ (the first $n$ samples are $\xi_0,\dots,\xi_{n-1}$) and $P_0$ is the law of $\xi_0$. Every $h\in\mathcal H$ is required to be $P_0$-integrable (needed for $E_{P_0}[h]$ to be defined). The supremum is taken in $[0,\infty]$, so an unbounded family of deviations cannot be hidden behind a junk value. Almost-sure convergence is Mathlib's `∀ᵐ`, which asks the exceptional set to have *outer* measure zero (no measurability of the supremum is assumed); this is the "outer almost sure" reading of $\text{a.s.}^*$.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 16, Definition 2

import Mathlib
import Definitions.Def_VarianceRegularization_Expansion_empMean

open MeasureTheory Filter Topology
open scoped ENNReal

namespace GenEmpLik.Consistency

/-- Definition 2 (arXiv:1610.03425v3, p. 16): a class `H` of functions `h : Ξ → ℝ` is
Glivenko–Cantelli for the sample `ξ₀, ξ₁, …` on `(Ω, μ)` (law `P₀ = μ.map (ξ 0)`) if every
`h ∈ H` is `P₀`-integrable and, almost surely,
`sup_{h ∈ H} |E_{P̂_n}[h] − E_{P₀}[h]| → 0`, where `P̂_n` is the empirical distribution of
`ξ₀, …, ξ_{n−1}`. The supremum is taken in `[0, ∞]`, so an unbounded family is not hidden
behind a junk value, and `∀ᵐ` bounds the outer measure of the exceptional set. -/
def IsGlivenkoCantelli {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ξ : ℕ → Ω → Ξ) (H : Set (Ξ → ℝ)) : Prop :=
  (∀ h ∈ H, Integrable h (μ.map (ξ 0))) ∧
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => ⨆ h ∈ H,
      ENNReal.ofReal |VarianceRegularization.Expansion.empMean (fun i : Fin n => h (ξ i ω))
        - ∫ s, h s ∂(μ.map (ξ 0))|) atTop (𝓝 0)

end GenEmpLik.Consistency



-- Prove2me | Definitions.Def_SparseBatchBandit_Regime
-- name    : SparseBatchBandit_Regime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:21.128379+00:00
-- url     : https://prove2.me/theorems/68752975-8420-44a3-a6b4-cb4559c0b47f
-- title:
--   The parameter regime of Theorem 2
-- statement:
--   The regime of Theorem 2 fixes $T\ge2$, $d\ge1$, $K\ge2$, $M\ge1$, $s_0\ge1$, $\gamma,\rho>0$, and, with constants $A,\varepsilon,\beta$ and a degree $p$,
--
--   1. (Assumption 3) $d\le AT^p$ and $s_0\le AT^{1-\varepsilon}$;
--   2. (Assumption 4) $\dfrac{\log K}{\gamma\rho}\le A\dfrac{d}{s_0}$ and $\dfrac{\log K}{\gamma\rho^3}\le A\sqrt{\dfrac{T^{1-\beta}}{s_0}}$;
--   3. $M\le A\max\{1,\log\log(T/s_0)\}$.
--
--   **Formalization Note** These are the paper's $\mathbf{Poly}$ and $O$ with the implied constants named, and $A,\varepsilon,\beta,p$ are fixed outside the instance in every theorem. The clauses on $s_0$ give $T/s_0\ge T^\varepsilon/A$, so $\log\log(T/s_0)$ is a logarithm of a negative number only on a bounded set of $T$; Lean's `Real.log` of a negative number is the logarithm of its absolute value, which there relaxes the bound on $M$ by a constant. `max 1` keeps the instances with $\log\log(T/s_0)\le1$.
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, Assumptions 3–4, p.6; Theorem 2, p.16

import Mathlib

namespace SparseBatchBandit

/-- The regime of Theorem 2 of Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4: the ranges of the parameters, Assumption 3 (p.6, PDF 6:
`d = Poly(T)`, `s₀ = O(T^{1−ε})`), Assumption 4 (p.6: `log K/(γρ) = O(d/s₀)`,
`log K/(γρ³) = O(√(T^{1−β}/s₀))`) and `M = O(log log(T/s₀))` (p.16, PDF 16), with the implied
constant of every `O` and the polynomial degree written out as `A` and `p`.

**Formalization Note.** `A, ε, β, p` are fixed outside the instance in every theorem, so a numerical
constant of the page may depend on them and on nothing else. `max 1` keeps instances with
`log log(T/s₀) ≤ 1`, whose `M` would otherwise be forced to `0`. The clauses on `s₀` give
`T/s₀ ≥ T^ε/A`; for the bounded set of `T` where that is below `1`, `Real.log` of a negative number
is `log` of its absolute value, which only relaxes the bound on `M` by a constant. -/
structure Regime (A ε β : ℝ) (p T d K M s₀ : ℕ) (γ ρ : ℝ) : Prop where
  /-- at least two rounds -/
  two_le_T : 2 ≤ T
  /-- the dimension is positive -/
  one_le_d : 1 ≤ d
  /-- at least two arms -/
  two_le_K : 2 ≤ K
  /-- at least one batch -/
  one_le_M : 1 ≤ M
  /-- the sparsity bound is positive -/
  one_le_s₀ : 1 ≤ s₀
  /-- `γ(K) > 0` -/
  γ_pos : 0 < γ
  /-- `ρ(K) > 0` -/
  ρ_pos : 0 < ρ
  /-- Assumption 3: `d = Poly(T)` -/
  d_poly : (d : ℝ) ≤ A * (T : ℝ) ^ p
  /-- Assumption 3: `s₀ = O(T^(1−ε))` -/
  s₀_le : (s₀ : ℝ) ≤ A * (T : ℝ) ^ (1 - ε)
  /-- Assumption 4, first bound -/
  actions_d : Real.log K / (γ * ρ) ≤ A * ((d : ℝ) / s₀)
  /-- Assumption 4, second bound -/
  actions_T : Real.log K / (γ * ρ ^ 3) ≤ A * Real.sqrt ((T : ℝ) ^ (1 - β) / s₀)
  /-- `M = O(log log(T/s₀))` -/
  batches : (M : ℝ) ≤ A * max 1 (Real.log (Real.log ((T : ℝ) / s₀)))

end SparseBatchBandit



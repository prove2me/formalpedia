-- Prove2me | Definitions.Def_SigmoidWire_RatApproxOn
-- name    : SigmoidWire_RatApproxOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:04:17.795218+00:00
-- url     : https://prove2.me/theorems/b8b1dd93-079a-417a-b241-b1830e364e06
-- title:
--   Univariate rational approximation on $[-a,a]$, and the hypothesis of Theorem 4.4
-- statement:
--   For $g:\mathbb R\to\mathbb R$, the statement $\mathrm{RatApproxOn}(g,a,k,\mathrm{err})$ says that there are real polynomials $P,Q$ of degree at most $k$ such that for every $x\in[-a,a]$,
--
--   $$
--   Q(x)\ne0\quad\text{and}\quad\Bigl|\frac{P(x)}{Q(x)}-g(x)\Bigr|\le\mathrm{err}.
--   $$
--
--   The **rational-approximation condition of Theorem 4.4** with constants $c,c_0$ says that for every integer $k\ge1$ and real $a\ge1$ there is a rational function of degree at most $k$, with no pole in $[-a,a]$, approximating $\sigma$ on $[-a,a]$ within
--
--   $$
--   c_0a^{c_0}\,e^{-k^{1/c}/c_0}.
--   $$
--
--   The shared definition lets the check that Sigmoid meets this condition visibly discharge the hypothesis of Theorem 4.4.
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 4.4 and Lemma 4.5, pp.19–20; Theorem B.3, p.60

import Mathlib

namespace SigmoidWire

/-- **Rational approximation on `[−a, a]`**: there is a rational function `P/Q` of degree at most
`k`, with no pole in `[−a, a]`, such that `|P(x)/Q(x) − g(x)| ≤ err` for every `x ∈ [−a, a]`.

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 4.4 and Lemma 4.5,
pp.19–20 (PDF pp.21–22), Theorem B.3, p.60 (PDF p.62); "the degree of a rational function `p/q` is
defined as `max{deg p, deg q}`" (p.19).

**Formalization Note.** A rational function is a pair of real polynomials `P, Q`; "degree at most
`k`" bounds both `natDegree`s; "no pole in `[−a, a]`" is `Q(x) ≠ 0` on `[−a, a]`. -/
def RatApproxOn (g : ℝ → ℝ) (a k err : ℝ) : Prop :=
  ∃ P Q : Polynomial ℝ, (P.natDegree : ℝ) ≤ k ∧ (Q.natDegree : ℝ) ≤ k ∧
    ∀ x ∈ Set.Icc (-a) a, Q.eval x ≠ 0 ∧ |P.eval x / Q.eval x - g x| ≤ err

/-- **The rational-approximation hypothesis of Theorem 4.4** with constants `c, c₀`: "For every
`k ≥ 1`, `a ≥ 1`, there is a rational function `r_k(x)` of degree at most `k` with no pole in
`[−a, a]` such that for every `x ∈ [−a, a]`, `|r_k(x) − σ(x)| ≤ c₀ a^{c₀} · e^{−k^{1/c}/c₀}`."

Li, Reichman, Williams, Wu, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 4.4,
p.19 (PDF p.21).

**Formalization Note.** `k` ranges over the natural numbers `k ≥ 1` (a degree), `a` over the reals
`a ≥ 1`; powers with real exponents are `Real.rpow`. -/
def RatApproxCond (σ : ℝ → ℝ) (c c₀ : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ a : ℝ, 1 ≤ a →
    RatApproxOn σ a k (c₀ * a ^ c₀ * Real.exp (-((k : ℝ) ^ (1 / c)) / c₀))

end SigmoidWire



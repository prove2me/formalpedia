-- Prove2me | Definitions.Def_SpikedWishart_LastPassage_Schur
-- name    : SpikedWishart_LastPassage_Schur
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:35:47.342238+00:00
-- url     : https://prove2.me/theorems/6100dc3c-1478-4f04-812a-e777d37c5d9e
-- title:
--   (310)–(311), pp. 1692–1693 — Schur functions s_λ(x) and the law of independent geometric site variables of parameter x_iy_j
-- statement:
--   This file defines the two objects of the geometric last passage formula (310).
--
--   1. **Schur functions.** A partition $\lambda$ is identified with its Young diagram. A semistandard Young tableau $T$ of shape $\lambda$ fills the cells with nonnegative integers, weakly increasing along rows and strictly increasing down columns. For finitely many variables $x_1, \ldots, x_n$, extended by $x_k = 0$ for $k > n$, the **Schur function** is
--   $$s_\lambda(x) = \sum_{T} \prod_{c\in\lambda} x_{T(c)},$$
--   the sum over all semistandard tableaux of shape $\lambda$. Only tableaux with all entries among the first $n$ indices contribute, so the sum is finite; $s_\lambda(x) = 0$ when $\lambda$ has more than $n$ rows.
--
--   2. **Geometric environment.** Given $x_1,\ldots,x_N$ and $y_1,\ldots,y_M$, the array $Y(i,j)$ of independent geometric random variables with $\mathbb P(Y(i,j) = k) = (1-x_iy_j)(x_iy_j)^k$, $k = 0, 1, 2, \ldots$, has the law on $\mathbb N^{N\times M}$ that gives each array $Y$ the probability $\prod_{i,j}(1-x_iy_j)(x_iy_j)^{Y(i,j)}$.
--
--   These are the ingredients of the Robinson–Schensted–Knuth formula (310) and of the Cauchy identity (311).
--
--   **Formalization Note** The Schur function is the combinatorial (tableau) definition, using Mathlib's `SemistandardYoungTableau`, with the variables extended by zero exactly as the paper sets $x_i = 0$ for $i > N$. Tableau entries are 0-based. The joint geometric law is written directly as the sum of point masses with product weights, which is the law of independent geometric variables.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), pp. 1692–1693, (310) and (311)

import Mathlib

namespace SpikedWishart.LastPassage

open MeasureTheory

/-- The variables `x = (x₀, …, x_{n-1})` extended by zero to an infinite sequence
(`x_k = 0` for `k ≥ n`). -/
noncomputable def extendByZero {n : ℕ} (x : Fin n → ℝ) (k : ℕ) : ℝ :=
  if h : k < n then x ⟨k, h⟩ else 0

/-- The Schur function `s_μ(x)` of the partition (Young diagram) `μ`, evaluated at the finitely many
variables `x`, extended by zero: the sum over all semistandard Young tableaux `T` of shape `μ` of
`∏_{cells c} x_{T(c)}`. Only tableaux with entries `< n` contribute, so the sum is finite. -/
noncomputable def schur {n : ℕ} (x : Fin n → ℝ) (μ : YoungDiagram) : ℝ :=
  ∑' T : SemistandardYoungTableau μ, ∏ c ∈ μ.cells, extendByZero x (T c.1 c.2)

/-- The joint law of an array `Y(i, j)` of independent geometric random variables with
`P(Y(i, j) = k) = (1 - x_i y_j) (x_i y_j)^k`, `k = 0, 1, 2, …`: the measure on arrays
`Fin N → Fin M → ℕ` giving each array the product of the site probabilities. -/
noncomputable def geomLaw {N M : ℕ} (x : Fin N → ℝ) (y : Fin M → ℝ) :
    Measure (Fin N → Fin M → ℕ) :=
  Measure.sum fun Y =>
    ENNReal.ofReal (∏ i, ∏ j, (1 - x i * y j) * (x i * y j) ^ Y i j) • Measure.dirac Y

end SpikedWishart.LastPassage



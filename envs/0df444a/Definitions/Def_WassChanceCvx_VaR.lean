-- Prove2me | Definitions.Def_WassChanceCvx_VaR
-- name    : WassChanceCvx_VaR
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:24:56.842619+00:00
-- url     : https://prove2.me/theorems/02b1f7a0-ebf5-40ce-903e-aa25060d0b05
-- title:
--   Value-at-risk $\mathrm{VaR}_\beta$ (lower quantile, Definition 5)
-- statement:
--   For a probability distribution $\mu$ on $\mathbb R$ (the law $\mathbb P_X$ of a random variable $X$) and a level $\beta$,
--
--   $$
--   \mathrm{VaR}_\beta(\mu)=\inf\{x\in\mathbb R:\ \mu\bigl((-\infty,x]\bigr)\ge\beta\}.
--   $$
--
--   The paper's $\mathrm{VaR}_{1-\epsilon}(X)$ is $\mathrm{VaR}_{1-\epsilon}(\mathbb P_X)$ and its $\mathrm{VaR}_\epsilon(X)$ is $\mathrm{VaR}_\epsilon(\mathbb P_X)$, the lower $\epsilon$-quantile.
--
--   **Formalization Note** The random variable enters through its law (`Measure.map` of a measurable map in the statements). For a probability measure and $\beta\in(0,1)$ the set is nonempty and bounded below, so the real infimum is the paper's (and is attained); other arguments give Lean's default value, which no statement uses.
-- source:
--   Shen, Jiang, Convex Chance-Constrained Programs with Wasserstein Ambiguity, arXiv:2111.02486v2, Definition 5, p.6

import Mathlib

open MeasureTheory

namespace WassChanceCvx

/-- **Value-at-risk (lower quantile).**
Shen, Jiang, arXiv:2111.02486v2, Definition 5, p.6: "Let `X` be a random variable, inducing
probability distribution `ℙ_X`. The `(1 − ϵ)`-VaR of `X` is defined through
`VaR_{1−ϵ}(X) := inf{x : ℙ_X[X ≤ x] ≥ 1 − ϵ}`."

`VaR β μ = inf{x ∈ ℝ : μ((−∞, x]) ≥ β}` for a law `μ` on `ℝ`. The paper's `VaR_{1−ϵ}(X)` is
`VaR (1 - ϵ) (law of X)` and its `VaR_ϵ(X)` is `VaR ϵ (law of X)`.

**Formalization Note.** The random variable enters only through its law `μ` (in the statements,
`Measure.map` of a measurable map). The infimum is `sInf` in `ℝ`: for a probability measure and
`β ∈ (0, 1)` the set is nonempty and bounded below, so this is the paper's infimum (attained);
for other arguments the value is Lean's junk `sInf`, which no statement uses. -/
noncomputable def VaR (β : ℝ) (μ : Measure ℝ) : ℝ :=
  sInf {x : ℝ | ENNReal.ofReal β ≤ μ (Set.Iic x)}

end WassChanceCvx



-- Prove2me | Definitions.Def_NonstatNV_IsTailSubGaussian
-- name    : NonstatNV_IsTailSubGaussian
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:01:54.275023+00:00
-- url     : https://prove2.me/theorems/035f03b0-5e76-41ec-abca-bc8dd6588efc
-- title:
--   Sub-Gaussian tail condition $P(|X|>x)\le 2e^{-x^2/K^2}$
-- statement:
--   A probability law $\nu$ on $\mathbb R$ satisfies the **sub-Gaussian tail condition with parameter $K$** if, for a random variable $X\sim\nu$,
--
--   $$
--   \mathbb P(|X|>x)\le 2\exp\!\left(-\frac{x^2}{K^2}\right)\qquad\text{for all } x\ge 0 .
--   $$
--
--   This is the paper's definition of a sub-Gaussian variable with sub-Gaussian norm at most $K$ (footnote 4), used in Assumption 1(b) and in Hoeffding's inequality (Lemma 3).
--
--   **Formalization Note** The inequality $|X|>x$ is strict, as printed. For $K=0$ the right side is read as $2$, so the condition is only meaningful for $K>0$; every use in the mission requires $K>0$.
-- source:
--   L. An, A. A. Li, B. Moseley, R. Ravi, The Nonstationary Newsvendor with (and without) Predictions, arXiv:2305.07993v4 (20 Feb 2025), https://arxiv.org/abs/2305.07993v4, footnote 4, p.10; Lemma 3, p.35

import Mathlib

open MeasureTheory

namespace NonstatNV

/-- The sub-Gaussian tail condition of footnote 4, p.10 (An, Li, Moseley, Ravi, *The Nonstationary Newsvendor with (and without) Predictions*, arXiv:2305.07993v4): a law `ν` on `ℝ` has
`P(|X| > x) ≤ 2 exp(−x²/K²)` for all `x ≥ 0`. A random variable is sub-Gaussian with
sub-Gaussian norm at most `K` when its law satisfies this with `K` (footnote 4; Lemma 3, p.35).

**Formalization Note** The strict inequality `x < |y|` is the printed `P(|X| > x)`. The condition is
only meaningful for `K > 0` (for `K = 0` the right side is `2`); every use of it in this
development requires `K > 0`. -/
def IsTailSubGaussian (ν : Measure ℝ) (K : ℝ) : Prop :=
  ∀ x : ℝ, 0 ≤ x → ν {y | x < |y|} ≤ ENNReal.ofReal (2 * Real.exp (-x ^ 2 / K ^ 2))

end NonstatNV



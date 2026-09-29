-- Prove2me | Definitions.Def_LeanEval_NumberTheory_LagariasElementaryCriterion
-- name    : LeanEval_NumberTheory_LagariasElementaryCriterion
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-06T02:07:43.355584+00:00
-- url     : https://prove2.me/theorems/17ada41a-3ac9-403e-87e5-12d4b55c8a94
-- title:
--   Lagarias elementary criterion (exact LeanEval definition)
-- statement:
--   For a positive integer $n$, let $\sigma(n)=\sum_{d\mid n}d$ and $H_n=\sum_{j=1}^n 1/j$. The Lagarias elementary criterion is the proposition
--
--   $$\forall n\in\mathbb N,\quad n>0\Longrightarrow \sigma(n)\le H_n+\exp(H_n)\log(H_n).$$
--
--   This definition names an arithmetic assertion; it does not assume or define the Riemann hypothesis. The inequality is non-strict, includes $n=1$, excludes $n=0$, and has no equality-only clause. Harmonic numbers are rational numbers cast to the reals, and the natural-valued divisor sum is also cast to the reals.
-- source:
--   Jeffrey C. Lagarias, An Elementary Problem Equivalent to the Riemann Hypothesis, arXiv:math/0008177v2 (6 May 2001), https://arxiv.org/abs/math/0008177v2, p. 1, Problem E, equation (1.1); the non-strict inequality only, exactly as in LeanEval statement revision 1.

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace LeanEval.NumberTheory

open scoped ArithmeticFunction.sigma

def LagariasElementaryCriterion : Prop :=
  ∀ n : ℕ,
    0 < n →
      ((σ 1 n : ℕ) : ℝ) ≤
        (harmonic n : ℝ) +
          Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ)

end LeanEval.NumberTheory



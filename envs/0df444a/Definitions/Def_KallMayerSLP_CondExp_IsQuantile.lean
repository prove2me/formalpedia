-- Prove2me | Definitions.Def_KallMayerSLP_CondExp_IsQuantile
-- name    : KallMayerSLP_CondExp_IsQuantile
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:10:23.72961+00:00
-- url     : https://prove2.me/theorems/22a0d4ae-1c32-46d2-848b-eee15501a7aa
-- title:
--   $\alpha$-quantile of a random variable
-- statement:
--   For a real random variable $\vartheta$ and $0<\alpha<1$, a real number $z$ is an **$\alpha$-quantile** of $\vartheta$ if both
--   $$
--   \mathbb P(\vartheta\le z)\ge\alpha\qquad\text{and}\qquad\mathbb P(\vartheta\ge z)\ge1-\alpha .
--   $$
--   The two inequalities together are what makes the quantile set an interval rather than a half-line.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §3, p.144

import Mathlib

open MeasureTheory

namespace KallMayerSLP.CondExp

/-- `z` is an `α`-quantile of the random variable `ϑ`: `ℙ(ϑ ≤ z) ≥ α` and `ℙ(ϑ ≥ z) ≥ 1 - α`.
Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §3, p.144 (PDF 154). -/
def IsQuantile {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (ϑ : Ω → ℝ) (α z : ℝ) : Prop :=
  α ≤ μ.real {ω | ϑ ω ≤ z} ∧ 1 - α ≤ μ.real {ω | z ≤ ϑ ω}

end KallMayerSLP.CondExp



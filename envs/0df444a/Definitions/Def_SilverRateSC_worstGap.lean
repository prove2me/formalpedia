-- Prove2me | Definitions.Def_SilverRateSC_worstGap
-- name    : SilverRateSC_worstGap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:45:17.658911+00:00
-- url     : https://prove2.me/theorems/25bab992-aa95-455c-be53-cd6eff2480b0
-- title:
--   Worst-case suboptimality ratio $E_{n,\kappa}(H)$, (1)
-- statement:
--   With the class $\mathscr F_{1/\kappa,1}(\mathbb R^d)$, the minimizer $x_*$ and the gradient-descent iterate $x_n$ as for $D_{n,\kappa}$, the **worst-case function-suboptimality ratio** of a schedule $H=(h_1,\dots,h_n)$ is
--   $$E_{n,\kappa}(H) := \sup_{d\in\mathbb N}\ \sup_{F\in\mathscr F_{1/\kappa,1}(\mathbb R^d)}\ \sup_{x_0\neq x_*}\ \frac{F(x_n)-F(x_*)}{F(x_0)-F(x_*)}.$$
--
--   It measures the worst relative decrease of the optimality gap that $n$ predetermined gradient steps can guarantee.
--
--   **Formalization Note** The supremum is taken in $[0,\infty]$ (finite by the verification file). For $x_0\ne x_*$ the denominator is positive by strong convexity, and the numerator is nonnegative, so the ratio is a nonnegative real.
-- source:
--   Liu, Ye, Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case, arXiv:2609.26873 (sha256 1e325f28…), §1.1, (1), p.5

import Mathlib
import Definitions.Def_SilverRateLB_gdRun
import Definitions.Def_HighResODE_NAGSC_FunctionClass

open scoped ENNReal

namespace SilverRateSC

/-- **Worst-case function-suboptimality ratio** `E_{n,κ}(H)`, (1):
`E_{n,κ}(H) := sup_{d ∈ ℕ} sup_{F ∈ F_{1/κ,1}(ℝ^d)} sup_{x_0 ≠ x_*} (F(x_n) − F(x_*)) / (F(x_0) − F(x_*))`,
with the class `F_{1/κ,1}(ℝ^d)`, the minimizer `x_*` and the iterate `x_n` as in `worstDist`.

Liu, Ye, *Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case*,
arXiv:2609.26873, §1.1, (1), p. 5.

**Formalization Note** The supremum is taken in `ℝ≥0∞` (no junk `0` for an unbounded family).
The class is `HighResODE.NAGSC.IsS1 F κ⁻¹ 1`, the minimizer is the binder `x_*` with
`∀ y, F x_* ≤ F y`, and `x_n` is `SilverRateLB.gdRun F H x₀`. The denominator is positive for
`x_0 ≠ x_*` by strong convexity, and the numerator is nonnegative, so `ENNReal.ofReal` loses
nothing. -/
noncomputable def worstGap (κ : ℝ) (H : List ℝ) : ℝ≥0∞ :=
  ⨆ (d : ℕ) (F : EuclideanSpace ℝ (Fin d) → ℝ) (_ : HighResODE.NAGSC.IsS1 F κ⁻¹ 1)
    (xs : EuclideanSpace ℝ (Fin d)) (_ : ∀ y, F xs ≤ F y)
    (x₀ : EuclideanSpace ℝ (Fin d)) (_ : x₀ ≠ xs),
    ENNReal.ofReal ((F (SilverRateLB.gdRun F H x₀) - F xs) / (F x₀ - F xs))

end SilverRateSC



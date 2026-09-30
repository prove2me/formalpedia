-- Prove2me | Definitions.Def_XuMannorRobust_Quantile_QuantileTruncatedMean
-- name    : XuMannorRobust_Quantile_QuantileTruncatedMean
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T16:06:22.400988+00:00
-- url     : https://prove2.me/theorems/f08ff57d-69f3-43bd-82f6-c519ff63083b
-- title:
--   $\beta$-quantile value $\mathbb Q^\beta(X)$ and $\beta$-truncated mean $\mathbb T^\beta(X)$ (Definition 3, corrected)
-- statement:
--   Let $X$ be a real random variable with law $P$ and let $\beta \in \mathbb R$. The **$\beta$-quantile value** of $X$ is
--
--   $$\mathbb Q^\beta(X) = \inf\{ c \in \mathbb R : \Pr(X \le c) \ge \beta \}.$$
--
--   Writing $Q = \mathbb Q^\beta(X)$, the **$\beta$-truncated mean** of $X$ is
--
--   $$\mathbb T^\beta(X) = \begin{cases} \mathbb E[X \cdot \mathbf 1(X < Q)] & \text{if } \Pr[X = Q] = 0, \\ \mathbb E[X \cdot \mathbf 1(X < Q)] + \big(\beta - \Pr[X < Q]\big)\, Q & \text{otherwise.} \end{cases}$$
--
--   For $\beta \in (0,1]$ and a nonnegative bounded $X$, $\mathbb Q^\beta(X)$ is the smallest value that is at least $X$ with probability at least $\beta$, and $\mathbb T^\beta(X)$ is the contribution to the expectation of $X$ of the leftmost $\beta$ fraction of its distribution. For example, if $X$ takes each of the values $c_1 < \dots < c_{10}$ with probability $0.1$, then $\mathbb Q^{0.63}(X) = c_7$ and $\mathbb T^{0.63}(X) = 0.1\big(\sum_{i=1}^6 c_i + 0.3\, c_7\big)$.
--
--   These two functionals replace the expected loss in the quantile-loss generalization bounds of Xu and Mannor (Theorems 2 and 5).
--
--   **Formalization Note** The paper's second branch reads $\big(\beta - \Pr[X < Q]\big)/\Pr[X = Q] \cdot Q$. That formula contradicts the paper's own worked example (it gives $0.1\sum_{i\le 6} c_i + 0.3\,c_7$ instead of $0.1\sum_{i \le 6} c_i + 0.03\,c_7$) and its verbal description; the division by $\Pr[X = Q]$ is dropped here, which is the reading the example, the verbal description and Appendix C use. Both functionals take the law $P$ as a measure on $\mathbb R$. Lean's `sInf` returns $0$ on a set that is empty or unbounded below, so $\mathbb Q^\beta = 0$ for $\beta \le 0$ (the paper's value would be $-\infty$) and for $\beta > 1$; every theorem of this mission uses levels in $[0,1]$ and nonnegative variables, where $\mathbb Q^0 = 0$ and $\mathbb T^0 = 0$ are harmless.
-- source:
--   Xu & Mannor, Robustness and Generalization, Mach Learn 86 (2012), DOI 10.1007/s10994-011-5268-1, p. 399, Definition 3 (second branch of the truncated mean corrected per the worked example on p. 399)

import Mathlib

open MeasureTheory

namespace XuMannorRobust.Quantile

/-- **β-quantile value** (Xu & Mannor 2012, p. 399, Definition 3). For the law `P` of a real random
variable `X`, `ℚ^β(X) = inf {c ∈ ℝ : Pr(X ≤ c) ≥ β}`, with `Pr(X ≤ c) = P((-∞, c])`.

Junk values: for `β ≤ 0` the set is all of `ℝ` (unbounded below) and Lean's `sInf` returns `0`
(the paper's value is `-∞`); for `β > 1` the set is empty and `sInf ∅ = 0`. -/
noncomputable def quantileValue (P : Measure ℝ) (β : ℝ) : ℝ :=
  sInf {c : ℝ | β ≤ (P (Set.Iic c)).toReal}

/-- **β-truncated mean** (Xu & Mannor 2012, p. 399, Definition 3, with the misprinted second branch
corrected). With `Q = ℚ^β(X)`:
`𝕋^β(X) = E[X · 1(X < Q)]` if `Pr[X = Q] = 0`, and
`𝕋^β(X) = E[X · 1(X < Q)] + (β − Pr[X < Q]) · Q` otherwise.
The paper prints `(β − Pr[X < Q]) / Pr[X = Q] · Q` in the second branch, which contradicts its own
worked example (0.63-truncated mean `0.1(∑_{i≤6} c_i + 0.3 c_7)`) and its verbal description (the
contribution to the expectation of the leftmost β fraction); the division is dropped here. -/
noncomputable def truncatedMean (P : Measure ℝ) (β : ℝ) : ℝ :=
  if P {quantileValue P β} = 0 then
    ∫ x in Set.Iio (quantileValue P β), x ∂P
  else
    (∫ x in Set.Iio (quantileValue P β), x ∂P) +
      (β - (P (Set.Iio (quantileValue P β))).toReal) * quantileValue P β

end XuMannorRobust.Quantile



-- Prove2me | Definitions.Def_IAFTRL_beta
-- name    : IAFTRL_beta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:41.44129+00:00
-- url     : https://prove2.me/theorems/177a85c2-7930-43bc-adb0-cfd97a0edd53
-- title:
--   Learning-rate scale $\beta_t$
-- statement:
--   For dimension $d$, $K$ actions and round $t\ge1$, the (inverse) learning rate of IA-FTRL is
--   $$
--   \beta_t=16d+\sqrt{\frac{dt}{1+\log K}} .
--   $$
--   It is nondecreasing in $t$ and depends only on $d$, $K$ and $t$.
--
--   **Formalization Note** The argument is the paper's 1-based round index; a 0-based Lean round $t$ uses $\beta_{t+1}$. The whole quotient $dt/(1+\log K)$ is under the square root.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Section 2.1, p.17

import Mathlib

namespace IAFTRL

/-- **The learning-rate scale `β_t`.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Section 2.1, p.17: "`β_t = 16d + √(dt/(1 + log K))`
is the (inverse) learning rate".

`beta d K t = 16d + √(d t / (1 + log K))`, with the paper's round index `t ≥ 1`.

**Formalization Note.** The whole quotient `dt/(1 + log K)` is under the square root (p.17,
rendered). The argument `t` is the paper's 1-based round; a 0-based Lean round `t` uses
`beta d K (t + 1)`. -/
noncomputable def beta (d K t : ℕ) : ℝ :=
  16 * (d : ℝ) + Real.sqrt ((d : ℝ) * t / (1 + Real.log K))

end IAFTRL



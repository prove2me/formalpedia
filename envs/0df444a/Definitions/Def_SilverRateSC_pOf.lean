-- Prove2me | Definitions.Def_SilverRateSC_pOf
-- name    : SilverRateSC_pOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:44:57.508065+00:00
-- url     : https://prove2.me/theorems/7e48ff6e-daba-47cf-baee-a9dbd68dedb3
-- title:
--   The exponent $p(c)=\log_2(1+\sqrt{1+c})$, (16)
-- statement:
--   For $1\le c\le2$ put
--   $$p(c) := \log_2\bigl(1+\sqrt{1+c}\bigr).$$
--   At $c=1$ this is the silver exponent $p_{\mathrm{sil}}=\log_2(1+\sqrt2)$. The exponent $p(c)$ governs the growth of the checkpoint costs in Appendix B and, through $c=c_\beta$, the block length $m\approx(\kappa/a_\beta)^{1/p(c_\beta)}$.
-- source:
--   Liu, Ye, Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case, arXiv:2609.26873 (sha256 1e325f28…), §4.1, (16), p.17

import Mathlib

namespace SilverRateSC

/-- **The exponent** `p(c) := log₂(1 + √(1 + c))`, (16). At `c = 1` it is the silver exponent
`p_sil = log₂(1 + √2)`.

Liu, Ye, *Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case*,
arXiv:2609.26873, §4.1, (16), p. 17: "Define p = p(c) := log2(1 + √(1+c))."

**Formalization Note** `log₂` is `Real.logb 2`; it is used with `1 ≤ c ≤ 2`, where the argument
is positive. -/
noncomputable def pOf (c : ℝ) : ℝ := Real.logb 2 (1 + Real.sqrt (1 + c))

end SilverRateSC



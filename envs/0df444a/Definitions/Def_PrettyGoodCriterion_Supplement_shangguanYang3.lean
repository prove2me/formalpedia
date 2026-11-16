-- Prove2me | Definitions.Def_PrettyGoodCriterion_Supplement_shangguanYang3
-- name    : PrettyGoodCriterion_Supplement_shangguanYang3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:32:00.768536+00:00
-- url     : https://prove2.me/theorems/b11d32a6-ce42-49cd-b0d5-f70c5c0c4028
-- title:
--   The Shangguan–Yang curve $B_3^{\mathrm{SY}}(\delta)$
-- statement:
--   Set $r_\delta:=\tfrac12-\sqrt{\delta(1-\delta)}$. The **Shangguan–Yang curve** for locality $w=3$ (Shangguan and Yang, Theorem 1.5, with their base-four entropy written in base-two logarithms) is
--   $$
--   B_3^{\mathrm{SY}}(\delta):=\begin{cases}\tfrac23, & r_\delta\ge\tfrac14,\\[2pt] -r_\delta\log_2 r_\delta-\dfrac{1-3r_\delta}{3}\log_2(1-3r_\delta), & 0<r_\delta<\tfrac14,\end{cases}\qquad(56)
--   $$
--   extended continuously by $B_3^{\mathrm{SY}}(\tfrac12):=0$ (where $r_{1/2}=0$). On $\tfrac25\le\delta<\tfrac12$ it is the $w=3$ upper bound on the rate of LDPC codes obtained by Shangguan and Yang; Theorem 4 (5) shows that the one-check PSC curve lies strictly below it on $[\tfrac16,\tfrac12)$.
--
--   **Formalization Note** Logarithms are `Real.logb 2`. For real $\delta$, $r_\delta\le0$ happens only at $\delta=\tfrac12$, so the last branch of the Lean definition (value $0$) is exactly the paper's $B_3^{\mathrm{SY}}(\tfrac12):=0$. For $\delta$ outside $[0,1]$ Lean's square root of a negative number is $0$ and the value is $\tfrac23$; the paper does not use the curve there.
-- source:
--   Alrabiah, Guruswami, Binary code rate bounds via classical–quantum channels, arXiv:2608.09347 (held version, sha256 e6d5ac13…), §8, equation (56), p.47 (PDF 49); Theorem 4 (5), p.5 (PDF 7)

import Mathlib

set_option autoImplicit false

namespace PrettyGoodCriterion.Supplement

/-- The **Shangguan–Yang curve** for `w = 3`, Alrabiah–Guruswami, *Binary code rate bounds via
classical–quantum channels*, arXiv:2608.09347 (held version), equation (56), p.47 (PDF 49)
([SY26, Theorem 1.5] in base-2 logarithms). With `r_δ := 1/2 − √(δ(1 − δ))`,
`B_3^SY(δ) := 2/3` if `r_δ ⩾ 1/4`, `:= −r_δ log r_δ − ((1 − 3r_δ)/3) log(1 − 3r_δ)` if
`0 < r_δ < 1/4`, extended continuously by `B_3^SY(1/2) := 0`.

**Formalization Note.** Logarithms are `Real.logb 2` (p.14). For real `δ`, `r_δ ⩽ 0` happens only at
`δ = 1/2` (where `r_δ = 0`), so the final branch `0` is exactly the paper's `B_3^SY(1/2) := 0`. For `δ`
outside `[0, 1]` the square root of a negative number is `0` in Lean and the value is `2/3`; the paper
does not use the curve there, and Theorem 4 (5) evaluates it only on `[1/6, 1/2)`. -/
noncomputable def shangguanYang3 (δ : ℝ) : ℝ :=
  let r : ℝ := 1 / 2 - Real.sqrt (δ * (1 - δ))
  if 1 / 4 ≤ r then 2 / 3
  else if 0 < r then -(r * Real.logb 2 r) - (1 - 3 * r) / 3 * Real.logb 2 (1 - 3 * r)
  else 0

end PrettyGoodCriterion.Supplement



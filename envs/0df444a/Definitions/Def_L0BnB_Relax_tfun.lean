-- Prove2me | Definitions.Def_L0BnB_Relax_tfun
-- name    : L0BnB_Relax_tfun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:46:56.781467+00:00
-- url     : https://prove2.me/theorems/39eb0df5-00cb-4b9a-a99e-31ff19984f1a
-- title:
--   The coordinate gap $t(\beta_i)$ in the proof of Proposition 2
-- statement:
--   For $\lambda_0,\lambda_2>0$ and $M>0$,
--
--   $$t(b)=2\lambda_0\,\mathcal B\bigl(b\sqrt{\lambda_2/\lambda_0}\bigr)-\frac{\lambda_0}{M}|b|-\lambda_2b^2,\qquad b\in\mathbb R .$$
--
--   It is the $i$-th summand of $G(\beta)-H(\beta)$, so the sign of $t$ on $[-M,M]$ decides how the two relaxations compare.
--
--   **Formalization Note** The dependence on $\lambda_0$, $\lambda_2$, $M$, implicit in the paper, is explicit.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, proof of Proposition 2, p. 29 (unnumbered)

import Mathlib
import Definitions.Def_L0BnB_Relax_reverseHuber

namespace L0BnB.Relax

/-- **The coordinate gap `t(βᵢ)` in the proof of Proposition 2.**
Hazimeh, Mazumder, Saab, *Sparse Regression at Scale: Branch-and-Bound rooted in First-Order
Optimization*, arXiv:2004.06152v2, proof of Proposition 2, p. 29 (unnumbered): "Define a function `t : ℝ → ℝ` as follows
`t(βi) := 2λ0B(βi√(λ2/λ0)) − (λ0/M)|βi| − λ2β²i`."

`tfun lam0 lam2 M b = 2λ₀ B(b √(λ₂/λ₀)) − (λ₀/M)|b| − λ₂ b²`; it is the `i`-th summand of
`G(β) − H(β)`.

**Formalization Note.** The dependence on `λ₀, λ₂, M`, implicit in the paper, is explicit. -/
noncomputable def tfun (lam0 lam2 M b : ℝ) : ℝ :=
  2 * lam0 * reverseHuber (b * Real.sqrt (lam2 / lam0)) - lam0 / M * |b| - lam2 * b ^ 2

end L0BnB.Relax



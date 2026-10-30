-- Prove2me | Definitions.Def_L0BnB_Relax_G
-- name    : L0BnB_Relax_G
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:41:59.176286+00:00
-- url     : https://prove2.me/theorems/ece98ed6-bee9-42a7-a2e0-e050874b6ec4
-- title:
--   The reduced objective $G(\beta)$ of (6)
-- statement:
--   For data $X\in\mathbb R^{n\times p}$, $y\in\mathbb R^n$ and $\lambda_0,\lambda_2>0$,
--
--   $$G(\beta)=\frac12\|y-X\beta\|_2^2+\sum_{i=1}^p\psi_1(\beta_i;\lambda_0,\lambda_2),\qquad \beta\in\mathbb R^p .$$
--
--   By (6), the value of the interval relaxation of PR$(\infty)$ is $\min_\beta G(\beta)$.
--
--   **Formalization Note** Only the function is defined. The identity $V_{PR(\infty)}=\min_\beta G(\beta)$ is a theorem of the mission, not part of the definition of $V_{PR(\infty)}$.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, eq. (6), p. 6

import Mathlib
import Definitions.Def_L0BnB_Relax_rss
import Definitions.Def_L0BnB_Relax_psi1

namespace L0BnB.Relax

/-- **The β-space objective `G(β)` of (6).**
Hazimeh, Mazumder, Saab, *Sparse Regression at Scale: Branch-and-Bound rooted in First-Order
Optimization*, arXiv:2004.06152v2, eq. (6), p. 6: "`G(β) := (1/2)‖y − Xβ‖²₂ + Σ_{i∈[p]} ψ1(βi; λ0, λ2)`".

`G X y lam0 lam2 β = ½‖y − Xβ‖²₂ + ∑ᵢ ψ₁(βᵢ; λ₀, λ₂)`.

**Formalization Note.** Only the function `G` is defined here. The identity
`V_PR(∞) = min_β G(β)` of (6) is a theorem of the mission (milestone (6)), not a definition:
`V_PR(∞)` is defined as the value of the interval relaxation of PR(∞) (`VPRinf`, paper.md
Reading 3). The squared norm is a sum of squares (`rss`). -/
noncomputable def G {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam0 lam2 : ℝ)
    (β : Fin p → ℝ) : ℝ :=
  rss X y β + ∑ i, psi1 lam0 lam2 (β i)

end L0BnB.Relax



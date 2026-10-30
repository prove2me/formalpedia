-- Prove2me | Definitions.Def_L0BnB_Relax_H
-- name    : L0BnB_Relax_H
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:46:33.39698+00:00
-- url     : https://prove2.me/theorems/93a58346-a30d-4a3f-8ea1-a6c1fbcbb5ce
-- title:
--   The reduced objective $H(\beta)$ of (37)
-- statement:
--   For $M>0$,
--
--   $$H(\beta)=\frac12\|y-X\beta\|_2^2+\sum_{i\in[p]}\Bigl(\frac{\lambda_0}{M}|\beta_i|+\lambda_2\beta_i^2\Bigr).$$
--
--   By (37), the value of the interval relaxation of B$(M)$ is the minimum of $H$ over the box $\|\beta\|_\infty\le M$.
--
--   **Formalization Note** Lean's division gives $\lambda_0/0=0$, so $H$ is only used with $M>0$.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, proof of Proposition 1, eq. (37), p. 28

import Mathlib
import Definitions.Def_L0BnB_Relax_rss

namespace L0BnB.Relax

/-- **The β-space objective `H(β)` of (37).**
Hazimeh, Mazumder, Saab, *Sparse Regression at Scale: Branch-and-Bound rooted in First-Order
Optimization*, arXiv:2004.06152v2, proof of Proposition 1, eq. (37), p. 28: "`H(β) := (1/2)‖y − Xβ‖²₂ +
Σ_{i∈[p]} ((λ0/M)|βi| + λ2β²i)`".

`H X y lam0 lam2 M β = ½‖y − Xβ‖²₂ + ∑ᵢ ((λ₀/M)|βᵢ| + λ₂ βᵢ²)`.

**Formalization Note.** Only the function is defined; the identity `V_B(M) = min_{‖β‖∞≤M} H(β)`
is a theorem of the mission, stated for `M > 0`. At `M = 0` Lean's `λ₀/0 = 0`, so `H` is used
only with `0 < M`. -/
noncomputable def H {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (β : Fin p → ℝ) : ℝ :=
  rss X y β + ∑ i, (lam0 / M * |β i| + lam2 * β i ^ 2)

end L0BnB.Relax



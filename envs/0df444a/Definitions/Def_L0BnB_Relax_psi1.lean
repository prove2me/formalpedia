-- Prove2me | Definitions.Def_L0BnB_Relax_psi1
-- name    : L0BnB_Relax_psi1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:41:22.332606+00:00
-- url     : https://prove2.me/theorems/7f828b72-2375-431b-a863-24c215680dfa
-- title:
--   The penalty $\psi_1(\beta_i;\lambda_0,\lambda_2)$ of Theorem 1
-- statement:
--   For regularization parameters $\lambda_0,\lambda_2>0$ and $b\in\mathbb R$,
--
--   $$\psi_1(b;\lambda_0,\lambda_2)=2\lambda_0\,\mathcal B\bigl(b\sqrt{\lambda_2/\lambda_0}\bigr),$$
--
--   where $\mathcal B$ is the reverse Huber penalty (4). It is the per-coordinate value of the interval relaxation of the perspective formulation without Big-M constraints.
--
--   **Formalization Note** `λ` is a Lean keyword, so the parameters are named `lam0`, `lam2`. The function is total; every theorem using it assumes $\lambda_0,\lambda_2>0$.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, Theorem 1, p. 6

import Mathlib
import Definitions.Def_L0BnB_Relax_reverseHuber

namespace L0BnB.Relax

/-- **The penalty `ψ₁(βᵢ; λ₀, λ₂) = 2λ₀ B(βᵢ √(λ₂/λ₀))`.**
Hazimeh, Mazumder, Saab, *Sparse Regression at Scale: Branch-and-Bound rooted in First-Order
Optimization*, arXiv:2004.06152v2, Theorem 1, p. 6: "`ψ1(βi; λ0, λ2) := 2λ0B(βi√(λ2/λ0))`".

`psi1 lam0 lam2 b = 2 λ₀ B(b √(λ₂/λ₀))` with `B` the reverse Huber penalty (4).

**Formalization Note.** `λ` is a Lean keyword, so the parameters are `lam0`, `lam2`. The
definition is total; every statement that uses it assumes `0 < lam0` and `0 < lam2`
(paper.md Reading 1), so `Real.sqrt (lam2 / lam0)` is the paper's square root. -/
noncomputable def psi1 (lam0 lam2 b : ℝ) : ℝ :=
  2 * lam0 * reverseHuber (b * Real.sqrt (lam2 / lam0))

end L0BnB.Relax



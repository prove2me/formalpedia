-- Prove2me | Definitions.Def_L0BnB_Relax_prObj
-- name    : L0BnB_Relax_prObj
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:44:09.790312+00:00
-- url     : https://prove2.me/theorems/9b649397-93ee-49a7-9a4c-e64c29e29dce
-- title:
--   Objective of the perspective formulation, eq. (3)
-- statement:
--   For $(\beta,z,s)\in(\mathbb R^p)^3$ the objective of the perspective formulation (3) is
--
--   $$\frac12\|y-X\beta\|_2^2+\lambda_0\sum_{i\in[p]}z_i+\lambda_2\sum_{i\in[p]}s_i ,$$
--
--   where each $s_i$ takes the place of $\beta_i^2$ in the ridge term.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, eq. (3), p. 5

import Mathlib
import Definitions.Def_L0BnB_Relax_rss

namespace L0BnB.Relax

/-- **Objective of the perspective formulation PR(M)**, eq. (3).
Hazimeh, Mazumder, Saab, *Sparse Regression at Scale: Branch-and-Bound rooted in First-Order
Optimization*, arXiv:2004.06152v2, eq. (3), p. 5: "`min_{β,z,s} (1/2)‖y − Xβ‖²₂ + λ0 Σ_{i∈[p]} zi + λ2 Σ_{i∈[p]} si`".

`prObj X y lam0 lam2 β z s = ½‖y − Xβ‖²₂ + λ₀ ∑ᵢ zᵢ + λ₂ ∑ᵢ sᵢ`. The objective does not involve
`M`. -/
noncomputable def prObj {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 : ℝ) (β z s : Fin p → ℝ) : ℝ :=
  rss X y β + lam0 * ∑ i, z i + lam2 * ∑ i, s i

end L0BnB.Relax



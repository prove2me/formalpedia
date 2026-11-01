-- Prove2me | Definitions.Def_VRAccelCLT_P2
-- name    : VRAccelCLT_P2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:21:11.234987+00:00
-- url     : https://prove2.me/theorems/ab56b60f-e39e-495c-928d-d3ece04ffb1b
-- title:
--   The matrix $P_2=\rho_2^{-1/2}H_2$ of Theorem 2
-- statement:
--   For $\rho_2>0$, $\alpha,\beta\in\mathbb R$ and $H\in\mathbb R^{m\times m}$,
--
--   $$
--   P_2=\rho_2^{-1/2}\begin{pmatrix}(1+\beta)(I_m-\alpha H) & -\beta(I_m-\alpha H)\\ I_m & 0_m\end{pmatrix}=\rho_2^{-1/2}H_2 .
--   $$
--
--   It is the transition matrix of the rescaled error $\rho_2^{-k/2}(y_k-x^*;\,y_{k-1}-x^*)$ in Theorem 2, and the limit covariance $\Sigma_2$ is built from its powers.
-- source:
--   Lei, Shanbhag, Variance-Reduced Accelerated First-order Methods: Central Limit Theorems and Confidence Statements, arXiv:2006.07769v3, Theorem 2, p.19

import Mathlib
import Definitions.Def_VRAccelCLT_accelBlock

namespace VRAccelCLT

/-- **The matrix `P₂`** of Theorem 2. Lei, Shanbhag, arXiv:2006.07769v3, Theorem 2, p.19:
"P2 ≜ ρ2^{−1/2} ((1 + β)(Im − αH)  −β(Im − αH) ; Im  0m)", i.e. `P₂ = ρ₂^{−1/2} H₂`.

**Formalization Note.** `ρ₂^{−1/2}` is the real power `ρ₂ ^ (−1/2 : ℝ)` (used with `ρ₂ > 0`). -/
noncomputable def P2 {m : ℕ} (ρ₂ α β : ℝ) (H : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ :=
  ρ₂ ^ (-(1 / 2 : ℝ)) • accelBlock α β H

end VRAccelCLT



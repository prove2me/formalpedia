-- Prove2me | Definitions.Def_VRAccelCLT_Sigma2
-- name    : VRAccelCLT_Sigma2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:21:57.773286+00:00
-- url     : https://prove2.me/theorems/b583e33c-2b8d-4147-b444-2cc99ce0a868
-- title:
--   The limit covariance $\Sigma_2$ of Theorem 2
-- statement:
--   For $\rho_2,\alpha,\beta$ and $H,S_0\in\mathbb R^{m\times m}$,
--
--   $$
--   \Sigma_2=\sum_{t=0}^{\infty}P_2^{t}\begin{pmatrix}S_0&0_m\\0_m&0_m\end{pmatrix}(P_2^{t})^{T},
--   $$
--
--   with $P_2=\rho_2^{-1/2}H_2$. It is the covariance of the Gaussian limit in Theorem 2. Only the top-left block of the middle matrix is $S_0$, because the noise enters only the first block of the stacked recursion.
-- source:
--   Lei, Shanbhag, Variance-Reduced Accelerated First-order Methods: Central Limit Theorems and Confidence Statements, arXiv:2006.07769v3, Theorem 2, p.19

import Mathlib
import Definitions.Def_VRAccelCLT_P2
import Definitions.Def_VRAccelCLT_lyapSum

namespace VRAccelCLT

/-- **The limit covariance `Σ₂`** of Theorem 2. Lei, Shanbhag, arXiv:2006.07769v3, Theorem 2, p.19:
"Σ2 ≜ Σ_{t=0}^{∞} P2^t (S0 0m ; 0m 0m) (P2^t)^T".

**Formalization Note.** `Σ₂ = lyapSum P₂ (fromBlocks S₀ 0 0 0)`; only the top-left block of the
middle matrix is `S₀`. -/
noncomputable def Sigma2 {m : ℕ} (ρ₂ α β : ℝ) (H S0 : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ :=
  lyapSum (P2 ρ₂ α β H) (Matrix.fromBlocks S0 0 0 0)

end VRAccelCLT



-- Prove2me | Definitions.Def_IncentiveFinNet_Q
-- name    : IncentiveFinNet_Q
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:18:03.908082+00:00
-- url     : https://prove2.me/theorems/b0459cc9-0d63-4cfd-9cda-1a2cb968ddc6
-- title:
--   The matrices $Q_i = \Psi_i^{\top}(2\gamma_i\Psi_i\Sigma_i\Psi_i^{\top})^{-1}\Psi_i$ and the best-response network
-- statement:
--   Fix a network setting $(\mu_i, \gamma_i, \Sigma_i, \Psi_i)_{i\in[n]}$ with expected-return matrix $M$. For each agent $i$ define
--   $$
--   Q_i = \Psi_i^{\top}\bigl(2\gamma_i\,\Psi_i\Sigma_i\Psi_i^{\top}\bigr)^{-1}\Psi_i .
--   $$
--   The matrix $\Psi_i\Sigma_i\Psi_i^{\top}$ is the principal submatrix of $\Sigma_i$ on the rows and columns $J_i$, hence positive definite, and $\gamma_i > 0$, so the inverse exists. When all edges are allowed, $\Psi_i = I_n$ and $Q_i = (2\gamma_i\Sigma_i)^{-1}$.
--
--   Given a price matrix $P$, the **best-response network** is the matrix whose $j$-th column holds agent $j$'s utility-maximizing contract sizes:
--   $$
--   W_{ij} = e_i^{\top} Q_j (M - P) e_j .
--   $$
--
--   $Q_i$ enters every matrix of Theorem 1, and the best-response network is the candidate stable network at prices $P$.
--
--   **Formalization Note** `⁻¹` is Mathlib's `Matrix.inv`, which returns $0$ on a singular matrix; by the remark above this never happens for a network setting, and no invertibility hypothesis is added. The module defines `Q` and `bestResponse`.
-- source:
--   Jalan, Chakrabarti, Sarkar, Incentive-Aware Models of Financial Networks, arXiv:2212.06808v3, §2.1, Q_i p.11; A.1, positive definiteness of Ψ_iΣ_iΨ_iᵀ and best-response display, p.33

import Mathlib
import Definitions.Def_IncentiveFinNet_NetworkSetting

open Matrix

namespace IncentiveFinNet

variable {n : ℕ}

/-- `Q_i = Ψ_iᵀ (2 γ_i Ψ_i Σ_i Ψ_iᵀ)⁻¹ Ψ_i`, arXiv:2212.06808v3, p.11 (repeated in A.1, p.33).

**Formalization Note** `⁻¹` is Mathlib's `Matrix.inv`. It is a genuine inverse here: `Ψ_i Σ_i Ψ_iᵀ`
is the principal submatrix of `Σ_i ≻ 0` on `J_i` (p.33), hence positive definite, and `γ_i > 0`.
No invertibility hypothesis is added. When `J_i = [n]`, `Q_i = (2γ_iΣ_i)⁻¹`. -/
noncomputable def Q (S : NetworkSetting n) (i : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  (S.Psi i)ᵀ * ((2 * S.γ i) • (S.Psi i * S.Sig i * (S.Psi i)ᵀ))⁻¹ * S.Psi i

/-- The best-response matrix of A.1, arXiv:2212.06808v3, p.33: given prices `P`, the matrix `W`
whose `j`-th column holds agent `j`'s utility-maximizing contract sizes,
`W_ij = e_iᵀ Q_j (M − P) e_j`. -/
noncomputable def bestResponse (S : NetworkSetting n) (P : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => (Q S j * (S.M - P)) i j

end IncentiveFinNet



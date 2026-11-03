-- Prove2me | Definitions.Def_IncentiveFinNet_matC
-- name    : IncentiveFinNet_matC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:17:16.226202+00:00
-- url     : https://prove2.me/theorems/e6171ba4-c10b-40d2-9f30-df1a076a8eff
-- title:
--   The matrices $B_{(i,j)} = e_ie_j^{\top}Q_i$ and $C_{(i,j)}$ of Theorem 1
-- statement:
--   Let $Q_1, \dots, Q_n$ be $n \times n$ real matrices and let $e_1,\dots,e_n$ be the standard basis of $\mathbb R^n$. For $i, j \in [n]$ define the $n\times n$ matrices
--   $$
--   B_{(i,j)} = e_i e_j^{\top} Q_i, \qquad C_{(i,j)} = \bigl(B_{(i,j)} - B_{(j,i)}\bigr) - \bigl(B_{(i,j)} - B_{(j,i)}\bigr)^{\top}.
--   $$
--   So $B_{(i,j)}$ has a single nonzero row, row $i$, equal to the $j$-th row of $Q_i$, and $C_{(i,j)}$ is skew-symmetric.
--
--   In Theorem 1, $Q_i$ is the network setting's matrix $Q_i = \Psi_i^{\top}(2\gamma_i\Psi_i\Sigma_i\Psi_i^{\top})^{-1}\Psi_i$; the rows of the matrix $Z_F$ of the linear system for the prices are the vectors $\mathrm{uvec}(C_{(i,j)})_F$.
--
--   **Formalization Note** The family $(Q_i)$ is a parameter, so that the trace identity of the proof can be stated for any symmetric family. $e_i$ is `Pi.single i 1` and $e_ie_j^{\top}$ is `vecMulVec`. The module defines `matB` and `matC`.
-- source:
--   Jalan, Chakrabarti, Sarkar, Incentive-Aware Models of Financial Networks, arXiv:2212.06808v3, Theorem 1, p.11; repeated in A.1, p.33

import Mathlib

open Matrix

namespace IncentiveFinNet

variable {n : ℕ}

/-- The matrix `B_{(i,j)} = e_i e_jᵀ Q_i` of Theorem 1, arXiv:2212.06808v3, p.11 (repeated in
A.1, p.33), built from a family `Q = (Q_i)_{i ∈ [n]}` of `n × n` matrices.

**Formalization Note** `e_i` is `Pi.single i 1` and `e_i e_jᵀ` is `vecMulVec e_i e_j`. The family
`Q` is a parameter; Theorem 1 uses the network setting's `Q_i`. -/
def matB (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  vecMulVec (Pi.single i 1) (Pi.single j 1) * Q i

/-- The matrix `C_{(i,j)} = (B_{(i,j)} − B_{(j,i)}) − (B_{(i,j)} − B_{(j,i)})ᵀ` of Theorem 1,
arXiv:2212.06808v3, p.11 (repeated in A.1, p.33). -/
def matC (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  (matB Q i j - matB Q j i) - (matB Q i j - matB Q j i)ᵀ

end IncentiveFinNet



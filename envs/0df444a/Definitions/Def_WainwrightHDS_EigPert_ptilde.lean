-- Prove2me | Definitions.Def_WainwrightHDS_EigPert_ptilde
-- name    : WainwrightHDS_EigPert_ptilde
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:25:56.20543+00:00
-- url     : https://prove2.me/theorems/2c94733c-69ab-4d7b-abf9-2df6ac71a3eb
-- title:
--   The off-diagonal block $\tilde p$ of $\widetilde{P} = U^\top P U$, Eq. (8.11)
-- statement:
--   Let $U$ and $P$ be real $d \times d$ matrices, $d \ge 1$. Write the transformed matrix in block form
--
--   $$
--   \widetilde{P} := U^\top P U = \begin{bmatrix} \tilde p_{11} & \tilde p^\top \\ \tilde p & \widetilde{P}_{22} \end{bmatrix},
--   \qquad \tilde p_{11} \in \mathbb{R},\ \tilde p \in \mathbb{R}^{d-1},\ \widetilde{P}_{22} \in \mathbb{R}^{(d-1)\times(d-1)} .
--   $$
--
--   The vector $\tilde p \in \mathbb{R}^{d-1}$ consists of the entries $(U^\top P U)_{i1}$, $i = 2, \dots, d$, of the first column of $\widetilde P$ below the diagonal. In Section 8.2.1, $U$ is the orthonormal matrix of eigenvectors of $\Sigma$ with first column $\theta^*$, so $\tilde p$ is the component of $P\theta^*$ orthogonal to $\theta^*$, written in the remaining eigenvectors; its Euclidean norm $\|\tilde p\|_2$ is the numerator of the perturbation bound (8.12).
--
--   **Formalization Note** The dimension is $d = n + 1$ and indices are 0-based: entry $i$ of `ptilde U P` (for `i : Fin n`) is the entry in row `i.succ`, column `0` of `Uᵀ * P * U`. The result lies in `EuclideanSpace ℝ (Fin n)`, so its norm is the Euclidean norm.
-- source:
--   Wainwright, High-Dimensional Statistics, Cambridge University Press 2019, Section 8.2.1, p. 242 (PDF p. 262), Eq. (8.11)

import Mathlib

namespace WainwrightHDS.EigPert

open Matrix

/-- **The off-diagonal block `p̃` of the transformed perturbation `P̃ = UᵀPU`**, Eq. (8.11).
Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
Press 2019, Section 8.2.1, p. 242 (PDF p. 262):
"`P̃ := UᵀPU = [p̃₁₁ p̃ᵀ; p̃ P̃₂₂]`, (8.11) where `p̃₁₁ ∈ ℝ`, `p̃ ∈ ℝ^{d−1}` and
`P̃₂₂ ∈ ℝ^{(d−1)×(d−1)}`".

`ptilde U P ∈ ℝ^{d−1}` is the first column of `UᵀPU` with its first entry `p̃₁₁` removed, i.e. the
entries `(UᵀPU)_{i1}` for `i = 2, …, d`.

**Formalization Note.** The dimension is `d = n + 1` and indices are 0-based: row `i.succ`
(`i : Fin n`) of column `0` of `Uᵀ * P * U` is the book's entry `(i+2, 1)`. The result lies in
`EuclideanSpace ℝ (Fin n)`, so `‖ptilde U P‖` is the Euclidean norm `‖p̃‖₂`. -/
noncomputable def ptilde {n : ℕ} (U P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => (Uᵀ * P * U) i.succ 0)

end WainwrightHDS.EigPert



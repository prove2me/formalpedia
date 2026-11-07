-- Prove2me | Definitions.Def_FreeSpencer_JPow
-- name    : FreeSpencer_JPow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:03:23.229968+00:00
-- url     : https://prove2.me/theorems/5d051cfa-e0f6-4ce5-b9e2-ba6eb1b6d7e5
-- title:
--   Powers of the operator $J_P=L_P+R_P$
-- statement:
--   For a real symmetric $P$, in an orthonormal eigenbasis with eigenvalues $p_i$, the operator $J_P^a$ on the full real matrix space multiplies the $(i,j)$ entry by $(p_i+p_j)^a$. So $J_P^{1/2}$ is the positive square root of $J_P=L_P+R_P$ and $J_P^{-1/2}$ is its inverse when $P\succ0$.
--
--   **Formalization Note** The operator does not depend on the eigenbasis chosen, being a function of the self-adjoint operator $J_P$.
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma 5.4, p.35

import Mathlib
import Definitions.Def_MatrixLewis_mpow
open scoped Matrix Matrix.Norms.L2Operator

namespace FreeSpencer

/-- The operator on the full real matrix space that, in an orthonormal eigenbasis of the symmetric
matrix `P` with eigenvalues `pᵢ`, multiplies the `(i, j)` entry by `(pᵢ + pⱼ)^a`. So `JPow P 1` is
`J_P = L_P + R_P`, `JPow P (1/2)` is its positive square root and `JPow P (-1/2)` the inverse of that.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma 5.4, p.35.

**Formalization Note** The operator does not depend on the eigenbasis, being a function of the
self-adjoint operator `J_P`. It is `0` on a matrix that is not symmetric; every statement has
`P ≻ 0`. -/
noncomputable def JPow {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℝ) (a : ℝ) :
    Module.End ℝ (Matrix ι ι ℝ) :=
  if h : P.IsHermitian then
    let U : Matrix ι ι ℝ := h.eigenvectorUnitary
    let W : Matrix ι ι ℝ := Matrix.of fun i j => (h.eigenvalues i + h.eigenvalues j) ^ a
    LinearMap.mulLeft ℝ U ∘ₗ LinearMap.mulRight ℝ Uᵀ ∘ₗ
      { toFun := fun X => W ⊙ X
        map_add' := fun X Y => Matrix.hadamard_add W X Y
        map_smul' := fun c X => by ext i j; simp [Matrix.hadamard_apply]; ring } ∘ₗ
      LinearMap.mulLeft ℝ Uᵀ ∘ₗ LinearMap.mulRight ℝ U
  else 0

end FreeSpencer



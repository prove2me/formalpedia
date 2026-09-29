-- Prove2me | Definitions.Def_CaiCandesShen_Convergence_Shrink
-- name    : CaiCandesShen_Convergence_Shrink
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:11:52.835615+00:00
-- url     : https://prove2.me/theorems/8c1834b0-d470-4ac9-b25e-61ee4ed47726
-- title:
--   Reduced SVD and the singular value shrinkage operator $\mathcal D_\tau$
-- statement:
--   Let $Y\in\mathbb R^{n_1\times n_2}$ have rank $r$. A **reduced singular value decomposition** of $Y$ is a factorization
--   $$Y = U\Sigma V^*,\qquad \Sigma=\operatorname{diag}(\{\sigma_i\}_{1\le i\le r}),$$
--   where $U$ and $V$ are $n_1\times r$ and $n_2\times r$ matrices with orthonormal columns ($U^*U = I_r$, $V^*V=I_r$) and the singular values $\sigma_i$ are positive.
--
--   For $\tau\ge 0$ the **singular value shrinkage operator** (soft-thresholding operator) is
--   $$\mathcal D_\tau(Y) := U\,\mathcal D_\tau(\Sigma)\,V^*,\qquad \mathcal D_\tau(\Sigma)=\operatorname{diag}(\{(\sigma_i-\tau)_+\}),$$
--   where $t_+=\max(0,t)$. It applies the scalar soft-thresholding rule to the singular values of $Y$, shrinking them toward zero and discarding those below $\tau$.
--
--   The relation "$X = \mathcal D_\tau(Y)$" is defined to hold when $X = U\operatorname{diag}((\sigma_i-\tau)_+)V^*$ for **some** reduced SVD $(U,\sigma,V)$ of $Y$. That this singles out exactly one $X$ (independently of the choice of SVD) is the separate well-definedness statement of the mission. $\mathcal D_\tau$ is the building block of every step of the SVT algorithm.
--
--   **Formalization Note** $\mathcal D_\tau$ is encoded as a relation `IsShrink τ Y X`, quantifying existentially over the rank $r$ and a reduced SVD, exactly as (2.1)–(2.2) define it. It deliberately does not mention the nuclear norm or any minimization, so that Theorem 2.1 (the proximal characterization) is a genuine theorem. The rank-$0$ case ($Y=0$, empty $U,V,\sigma$) is included.
-- source:
--   Cai, Candès, Shen, A Singular Value Thresholding Algorithm for Matrix Completion, SIAM J. Optim. 20 (2010), p. 1959, §2.1, Eqs. (2.1)–(2.2)

import Mathlib
import Definitions.Def_CaiCandesShen_Convergence_Basic

namespace CaiCandesShen.Convergence

open Matrix

/-- `(U, σ, V)` is a reduced singular value decomposition of `Y` of rank `r` (eq. (2.1), p. 1959):
`U` is `n₁ × r` and `V` is `n₂ × r` with orthonormal columns, the singular values `σ_i` are
positive, and `Y = U diag(σ) V*`. -/
def IsReducedSVD {n₁ n₂ : ℕ} (Y : Mat n₁ n₂) (r : ℕ) (U : Matrix (Fin n₁) (Fin r) ℝ)
    (σ : Fin r → ℝ) (V : Matrix (Fin n₂) (Fin r) ℝ) : Prop :=
  Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ (∀ i, 0 < σ i) ∧ Y = U * diagonal σ * Vᵀ

/-- `X = D_τ(Y)`, the singular value shrinkage (soft-thresholding) operator of eq. (2.2), p. 1959:
for some reduced SVD `Y = U diag(σ) V*`, `X = U diag((σ_i - τ)_+) V*`, where `t_+ = max(0, t)`. -/
def IsShrink {n₁ n₂ : ℕ} (τ : ℝ) (Y X : Mat n₁ n₂) : Prop :=
  ∃ (r : ℕ) (U : Matrix (Fin n₁) (Fin r) ℝ) (σ : Fin r → ℝ) (V : Matrix (Fin n₂) (Fin r) ℝ),
    IsReducedSVD Y r U σ V ∧ X = U * diagonal (fun i => max (σ i - τ) 0) * Vᵀ

end CaiCandesShen.Convergence



-- Prove2me | Definitions.Def_HighDimStat_SparseLinear_IsLagrangianLassoSolution
-- name    : HighDimStat_SparseLinear_IsLagrangianLassoSolution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:08:23.486307+00:00
-- url     : https://prove2.me/theorems/cb5c9de0-3d1f-4462-9cc7-2c6d7c13f1f0
-- title:
--   theta-hat solves the Lagrangian Lasso program (7.18)
-- statement:
--   This predicate says $\hat\theta$ is an optimal solution of the **Lagrangian Lasso**
--   program (7.18): $\hat\theta$ minimizes the penalized least-squares objective over all of
--   $\mathbb R^d$.
--
--   For $X \in \mathbb R^{n\times d}$, $y \in \mathbb R^n$, $\lambda_n \in \mathbb R$, and
--   $\hat\theta \in \mathbb R^d$,
--
--   $$
--   \hat\theta \text{ solves (7.18) for } (X,y,\lambda_n) \;:\Longleftrightarrow\; \forall
--   \beta \in \mathbb R^d,\quad \frac{1}{2n}\|y - X\hat\theta\|_2^2 + \lambda_n\|\hat\theta\|_1
--   \;\le\; \frac{1}{2n}\|y-X\beta\|_2^2 + \lambda_n\|\beta\|_1.
--   $$
--
--   This is the hypothesis on $\hat\theta$ that Theorem 7.13(a) bounds $\|\hat\theta -
--   \theta^*\|_2$ under.
--
--   **Formalization Note** Stated as global optimality over $\beta \in \mathbb R^d$ (an
--   unconstrained convex program), matching (7.18)'s own `argmin` over all of $\mathbb R^d$;
--   no additional convexity or differentiability structure is assumed, since none is needed to
--   state (only to prove) the optimality condition.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 206 (PDF p. 226), Eq. (7.18)

import Mathlib
import Definitions.Def_HighDimStat_SparseLinear_L1Norm

namespace HighDimStat.SparseLinear

/-- `θhat` is an optimal solution of the Lagrangian Lasso program (7.18),
`argmin_θ (1/(2n))‖y − Xθ‖₂² + λₙ‖θ‖₁`, of Wainwright, *High-Dimensional Statistics* (2019),
p. 206: `θhat` attains the minimum of the Lagrangian objective over all of `ℝ^d`. -/
def IsLagrangianLassoSolution {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ)
    (lam : ℝ) (θhat : Fin d → ℝ) : Prop :=
  ∀ β : Fin d → ℝ,
    (1 / (2 * (n : ℝ))) * (∑ i, (y i - X.mulVec θhat i) ^ 2) + lam * l1Norm θhat ≤
    (1 / (2 * (n : ℝ))) * (∑ i, (y i - X.mulVec β i) ^ 2) + lam * l1Norm β

end HighDimStat.SparseLinear



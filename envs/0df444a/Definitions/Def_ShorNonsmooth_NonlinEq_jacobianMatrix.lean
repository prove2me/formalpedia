-- Prove2me | Definitions.Def_ShorNonsmooth_NonlinEq_jacobianMatrix
-- name    : ShorNonsmooth_NonlinEq_jacobianMatrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T13:07:54.187607+00:00
-- url     : https://prove2.me/theorems/9e2b32c7-f708-4a15-bb0c-c78e6d922a2c
-- title:
--   The Jacobian matrix $J(x)=\{\partial\psi_i/\partial t_j\}$
-- statement:
--   For functions $\psi_1, \dots, \psi_n : E_n \to \mathbb{R}$ and a point $x = \{t_1, \dots, t_n\} \in E_n$, the **Jacobian** of the system $\psi_i(x) = 0$ at $x$ is the $n \times n$ matrix of partial derivatives
--   $$
--   J(x) = \left\{ \frac{\partial \psi_i}{\partial t_j}(x) \right\}_{i,j=1}^{n}.
--   $$
--   In the regular case of Section 3.5 it is assumed nonsingular at the solution.
--
--   **Formalization Note** Entry $(i,j)$ is `fderiv ℝ (ψ i) x (EuclideanSpace.single j 1)`, the derivative of $\psi_i$ at $x$ in the direction of the $j$-th coordinate vector. It is the partial derivative whenever $\psi_i$ is differentiable at $x$, which every theorem using it assumes.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 63 (the Jacobian J(x) of the regular case); p. 65 (det J(x) in Theorem 3.9)

import Mathlib

namespace ShorNonsmooth.NonlinEq

/-- Shor (1985), p. 63: the Jacobian `J(x) = {∂ψ_i/∂t_j}` of the system `ψ_i(x) = 0`,
`x = {t_1, …, t_n}`. Entry `(i, j)` is the partial derivative of `ψ_i` with respect to the
coordinate `t_j`, i.e. the Fréchet derivative of `ψ_i` at `x` applied to the `j`-th standard
basis vector. -/
noncomputable def jacobianMatrix {n : ℕ} (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => fderiv ℝ (ψ i) x (EuclideanSpace.single j 1)

end ShorNonsmooth.NonlinEq



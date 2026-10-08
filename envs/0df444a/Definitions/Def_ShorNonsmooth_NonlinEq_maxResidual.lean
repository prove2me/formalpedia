-- Prove2me | Definitions.Def_ShorNonsmooth_NonlinEq_maxResidual
-- name    : ShorNonsmooth_NonlinEq_maxResidual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T13:07:39.815447+00:00
-- url     : https://prove2.me/theorems/e151730a-8871-4039-9bf8-fd336e0c0207
-- title:
--   The max-residual function $f(x)=\max_i|\psi_i(x)|$ of a system of equations, (3.24)
-- statement:
--   Let $E_n$ be the $n$-dimensional Euclidean space and let $\psi_1, \dots, \psi_n : E_n \to \mathbb{R}$ be the left-hand sides of the system of equations
--   $$
--   \psi_i(x) = 0, \qquad i = 1, \dots, n, \qquad x = \{t_1, \dots, t_n\}.
--   $$
--   The system is solved by minimizing the nonsmooth function
--   $$
--   f(x) = \max_{1 \le i \le n} |\psi_i(x)| ,
--   $$
--   whose minimum value is $f^* = 0$ exactly when the system is consistent; its minimum points are then the solutions of the system.
--
--   This is the merit function in which the regular case of Section 3.5 and Theorems 3.8–3.9 are stated.
--
--   **Formalization Note** $E_n$ is `EuclideanSpace ℝ (Fin n)`, and the equations are indexed by `Fin n`, so `ψ i` is the book's $\psi_{i+1}$. The maximum is `⨆ i, |ψ i x|` over the finite index type; for $n \ge 1$ it is the book's maximum (for $n = 0$ it is $0$).
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, pp. 62-63, Eqs. (3.23)-(3.24)

import Mathlib

namespace ShorNonsmooth.NonlinEq

/-- Shor (1985), p. 63, Eq. (3.24): the nonsmooth merit function of the system
`ψ_i(x) = 0, i = 1, …, n` (3.23), `f(x) = max_{1 ≤ i ≤ n} |ψ_i(x)|`.
The equations are indexed by `Fin n` (index `i` here is the book's `i + 1`). -/
noncomputable def maxResidual {n : ℕ} (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⨆ i, |ψ i x|

end ShorNonsmooth.NonlinEq



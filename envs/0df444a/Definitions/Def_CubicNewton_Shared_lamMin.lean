-- Prove2me | Definitions.Def_CubicNewton_Shared_lamMin
-- name    : CubicNewton_Shared_lamMin
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T23:14:14.881006+00:00
-- url     : https://prove2.me/theorems/92b021f8-6b9f-4dd7-9c1a-19da185471b5
-- title:
--   Smallest eigenvalue $\lambda_n(A)$ as the Rayleigh-quotient infimum
-- statement:
--   For a linear operator $A$ on $\mathbb{R}^n$ define
--   $$\lambda_{\min}(A) = \inf_{\|v\| = 1} \langle A v, v\rangle .$$
--   For a self-adjoint $A$ this is the smallest eigenvalue, which the paper writes $\lambda_n(A)$ because it numbers eigenvalues decreasingly, $\lambda_1(A) \ge \dots \ge \lambda_n(A)$. In particular $A \succeq 0$ if and only if $\lambda_n(A) \ge 0$. The Hessian of a twice differentiable function is self-adjoint, so this is the quantity entering the optimality measure $\mu_M$.
--
--   Used by two missions of this paper: 01-nonconvex (the optimality measure $\mu_M$, p. 184) and 04-local-quadratic (the measure $\delta_k$ and the condition $f''(x_0) \succ 0$ of Theorem 3, pp. 186–187); the notation is that of p. 180.
--
--   **Formalization Note** For $n \ge 1$ the unit sphere is nonempty and $\langle Av, v\rangle \ge -\|A\|$ on it, so the infimum is a genuine infimum. For $n = 0$ the sphere is empty and Lean's real infimum returns $0$.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 180, Notation (eigenvalues numbered decreasingly, λn the smallest)

import Mathlib

open scoped RealInnerProductSpace

namespace CubicNewton.Shared

/-- The smallest eigenvalue `λₙ(A)` of a (self-adjoint) operator on `ℝⁿ`, written as the
Rayleigh-quotient infimum `inf_{‖v‖ = 1} ⟨A v, v⟩` (Nesterov–Polyak 2006, p. 180, Notation:
eigenvalues are numbered decreasingly, so `λₙ` is the smallest). For `n ≥ 1` the unit sphere is
nonempty and the quadratic form is bounded below by `−‖A‖`, so this is a genuine infimum; for
`n = 0` the sphere is empty and Lean's real `⨅` returns `0`. -/
noncomputable def lamMin {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⨅ v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, ⟪A v, v⟫

end CubicNewton.Shared



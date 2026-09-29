-- Prove2me | Definitions.Def_ProxNewton_Inexact_Method
-- name    : ProxNewton_Inexact_Method
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:37:04.122909+00:00
-- url     : https://prove2.me/theorems/9fc29a5f-6151-4189-9a93-0c76193d2392
-- title:
--   Inexact proximal Newton method with unit steps: stopping condition (2.24) and forcing terms (2.25)
-- statement:
--   Fix $M > 0$ and a sequence of forcing terms $(\eta_k)_{k\ge0}$. Let $\hat f_k = \hat g_k + h$ be the second-order model of $f$ at $x_k$ with the exact Hessian $\nabla^2 g(x_k)$.
--
--   1. **Adaptive stopping condition** (Eq. (2.24)). A search direction $\Delta x_k$ at $x_k$ satisfies
--   $$\big\|G_{\hat f_k/M}(x_k+\Delta x_k)\big\| \le \eta_k\,\big\|G_{f/M}(x_k)\big\|.$$
--   2. **A run of the inexact proximal Newton method with unit step lengths** is a pair of sequences $(x_k)$, $(\Delta x_k)$ with $x_0\in\operatorname{dom} h$ and, for every $k\ge0$: $\Delta x_k$ satisfies (2.24), $x_k+\Delta x_k\in\operatorname{dom}h$, and $x_{k+1} = x_k+\Delta x_k$. No other condition is placed on $\Delta x_k$.
--   3. **Forcing terms** (Eq. (2.25)). For $k\ge1$,
--   $$\eta_k = \min\left\{\frac m2,\ \frac{\|G_{\hat f_{k-1}/M}(x_k) - G_{f/M}(x_k)\|}{\|G_{f/M}(x_{k-1})\|}\right\}.$$
--
--   The stopping condition generalizes the inexact Newton condition $\|\nabla\hat g_k(x_k+\Delta x_k)\|\le\eta_k\|\nabla g(x_k)\|$ (2.23) to composite functions; the choice (2.25) is the Eisenstat–Walker forcing term.
--
--   **Formalization Note** Indices start at $k = 0$. The run is `IsInexactProxNewtonRun g D h M η x Δ`. `ewForcingTerm g D h M m x k` is the right-hand side of (2.25) for index $k+1$ (it uses $x_k$ and $x_{k+1}$); (2.25) does not define $\eta_0$. When $G_{f/M}(x_k)=0$, i.e. $x_k = x^\star$, Lean's division gives the quotient the value $0$, so $\eta_{k+1} = 0$ (an exact solve).
-- source:
--   Lee, Sun & Saunders, Proximal Newton-type methods for minimizing composite functions, arXiv:1206.1623v13, p. 9, Eq. (2.24) and Eq. (2.25); p. 15, §3.4 (unit step lengths)

import Mathlib
import Definitions.Def_ProxNewton_Inexact_CompositeStep

namespace ProxNewton.Inexact

open scoped RealInnerProductSpace

variable {n : ℕ}

/-- The adaptive stopping condition (2.24) at iterate `x_k` for the search direction `Δx_k`
and forcing term `η_k`: `‖G_{f̂_k/M}(x_k + Δx_k)‖ ≤ η_k ‖G_{f/M}(x_k)‖`, where `f̂_k = ĝ_k + h`
is the model with the exact Hessian `∇²g(x_k)`. -/
def StoppingCondition (g : EuclideanSpace ℝ (Fin n) → ℝ) (D : Set (EuclideanSpace ℝ (Fin n)))
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (M ηk : ℝ) (xk Δk : EuclideanSpace ℝ (Fin n)) : Prop :=
  ‖scaledStep (quadModel g xk) D h M (xk + Δk)‖ ≤ ηk * ‖scaledStep g D h M xk‖

/-- A run of the inexact proximal Newton method with unit step lengths, forcing terms `η`
and constant `M` in (2.24): `x_0 ∈ dom h`, and for every `k` the search direction `Δx_k`
satisfies (2.24), `x_k + Δx_k ∈ dom h`, and `x_{k+1} = x_k + Δx_k`. -/
def IsInexactProxNewtonRun (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (M : ℝ)
    (η : ℕ → ℝ) (x Δ : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  x 0 ∈ D ∧ ∀ k, x k + Δ k ∈ D ∧ StoppingCondition g D h M (η k) (x k) (Δ k) ∧
    x (k + 1) = x k + Δ k

/-- The forcing term (2.25) for iteration `k + 1`:
`η_{k+1} = min { m/2, ‖G_{f̂_k/M}(x_{k+1}) - G_{f/M}(x_{k+1})‖ / ‖G_{f/M}(x_k)‖ }`.
(When `G_{f/M}(x_k) = 0` the quotient is `0`.) -/
noncomputable def ewForcingTerm (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (M m : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (k : ℕ) : ℝ :=
  min (m / 2)
    (‖scaledStep (quadModel g (x k)) D h M (x (k + 1)) - scaledStep g D h M (x (k + 1))‖ /
      ‖scaledStep g D h M (x k)‖)

end ProxNewton.Inexact



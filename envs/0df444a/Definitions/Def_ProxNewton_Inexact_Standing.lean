-- Prove2me | Definitions.Def_ProxNewton_Inexact_Standing
-- name    : ProxNewton_Inexact_Standing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:36:27.958392+00:00
-- url     : https://prove2.me/theorems/716c40df-1b4f-46bb-a643-9cfcd36e7b5c
-- title:
--   Optimal solution of (1.1) and the standing assumptions of §3.4
-- statement:
--   Let $f = g + h$ be as in problem (1.1), with the nonsmooth part $h$ described by its domain $D$.
--
--   1. **Optimal solution.** $x^\star$ is an optimal solution of (1.1) when $x^\star\in D$ and $g(x^\star)+h(x^\star)\le g(y)+h(y)$ for all $y\in D$.
--   2. **Standing assumptions of §3.4** on the smooth part, with constants $m, L_1, L_2$: $g$ is twice continuously differentiable; $g$ is strongly convex with constant $m>0$ in the sense of Definition 3.2,
--   $$g(y) \ge g(x) + \nabla g(x)^T(y-x) + \frac m2\|x-y\|^2\quad\text{for all } x,y;$$
--   $\nabla g$ is Lipschitz continuous with constant $L_1\ge 0$, i.e. $\|\nabla g(x)-\nabla g(y)\|\le L_1\|x-y\|$; and $\nabla^2 g$ is Lipschitz continuous with constant $L_2\ge0$ in the operator norm, $\|\nabla^2 g(x)-\nabla^2 g(y)\|\le L_2\|x-y\|$.
--   3. **Upper Hessian bound.** $\nabla^2 g(x)\preceq MI$ for all $x$, i.e. $v^T\nabla^2 g(x)v\le M\|v\|^2$ for all $x, v$.
--
--   Item 2 collects assumptions (i) and (ii) stated once at the top of §3.4; item 3 is the condition "$H_k \preceq MI$" under which the stopping condition (2.24) is posed, for the exact Hessians $H_k = \nabla^2 g(x_k)$.
--
--   **Formalization Note** The page's (ii) reads "g and $\nabla^2 g$ are Lipschitz continuous with constants $L_1$ and $L_2$"; the notation paragraph of §3 (p. 10) and §3.2 (p. 11) say that $L_1$ is the Lipschitz constant of $\nabla g$, which is what is encoded. The structure is `SmoothPartAssumptions g m L1 L2`; the Hessian bound is `HessianLE g M`.
-- source:
--   Lee, Sun & Saunders, Proximal Newton-type methods for minimizing composite functions, arXiv:1206.1623v13, p. 3 (standing assumptions of §2, optimal solution x⋆); p. 11, Definition 3.2; p. 15, standing assumptions (i)–(ii) of §3.4; p. 9, Eq. (2.24) (H_k ⪯ MI)

import Mathlib
import Definitions.Def_ProxNewton_Inexact_CompositeStep

namespace ProxNewton.Inexact

open scoped RealInnerProductSpace

variable {n : ℕ}

/-- `x⋆` is an optimal solution of problem (1.1): it lies in the domain `D` of `h` and minimizes
`f = g + h` over `D` (hence over the whole space, `f = +∞` off `D`). -/
def IsMinimizer (g : EuclideanSpace ℝ (Fin n) → ℝ) (D : Set (EuclideanSpace ℝ (Fin n)))
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (xstar : EuclideanSpace ℝ (Fin n)) : Prop :=
  xstar ∈ D ∧ ∀ y ∈ D, g xstar + h xstar ≤ g y + h y

/-- The standing assumptions (i)–(ii) of §3.4 on the smooth part `g`: `g` is twice continuously
differentiable and strongly convex with constant `m > 0` in the sense of Definition 3.2, and `∇g`
and `∇²g` are Lipschitz continuous with constants `L1` and `L2`. -/
structure SmoothPartAssumptions (g : EuclideanSpace ℝ (Fin n) → ℝ) (m L1 L2 : ℝ) : Prop where
  contDiff : ContDiff ℝ 2 g
  m_pos : 0 < m
  strongConvex : ∀ x y, g x + ⟪gradient g x, y - x⟫ + m / 2 * ‖x - y‖ ^ 2 ≤ g y
  L1_nonneg : 0 ≤ L1
  grad_lipschitz : ∀ x y, ‖gradient g x - gradient g y‖ ≤ L1 * ‖x - y‖
  L2_nonneg : 0 ≤ L2
  hessian_lipschitz : ∀ x y, ‖hessian g x - hessian g y‖ ≤ L2 * ‖x - y‖

/-- `∇²g(x) ⪯ M I` for every `x`: `vᵀ ∇²g(x) v ≤ M ‖v‖²`. -/
def HessianLE (g : EuclideanSpace ℝ (Fin n) → ℝ) (M : ℝ) : Prop :=
  ∀ x v, ⟪hessian g x v, v⟫ ≤ M * ‖v‖ ^ 2

end ProxNewton.Inexact



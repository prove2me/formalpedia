-- Prove2me | Definitions.Def_HomotopyProxVM_parametrizedFn
-- name    : HomotopyProxVM_parametrizedFn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:35:54.730608+00:00
-- url     : https://prove2.me/theorems/e1093514-df6b-448f-818f-7c16227e1815
-- title:
--   The parametrization $f_\tau$ of $f$, (7)
-- statement:
--   Given a vector $\xi^0$, the **parametrized function** is, for $\tau\in[0,1]$,
--
--   $$
--   f_\tau(x):=\tau f(x)-(1-\tau)\langle\xi^0,x\rangle .
--   $$
--
--   So $f_1=f$ and $\nabla f_\tau(x)=\tau\nabla f(x)-(1-\tau)\xi^0$. In the paper $\xi^0$ is a subgradient of $g$ at the starting point, which makes the starting point a solution of the problem at $\tau=0$.
--
--   **Formalization Note** The definition takes any vector $\xi^0$ and any real $\tau$; the conditions are hypotheses of the theorems.
-- source:
--   Tran-Dinh, Liang & Toh, A New Homotopy Proximal Variable-Metric Framework for Composite Convex Minimization, arXiv:1812.05243v1, §3.1, (7), p.6

import Mathlib

open scoped RealInnerProductSpace

namespace HomotopyProxVM

/-- The parametrization (7) of `f`: `f_τ(x) := τ f(x) − (1 − τ)⟨ξ⁰, x⟩`
(Tran-Dinh, Liang & Toh, arXiv:1812.05243v1, §3.1, (7), p.6). The vector `ξ` is the fixed subgradient `ξ⁰ ∈ ∂g(x⁰)`; the
definition itself takes any vector. -/
noncomputable def parametrizedFn {p : ℕ} (f : EuclideanSpace ℝ (Fin p) → ℝ)
    (ξ : EuclideanSpace ℝ (Fin p)) (τ : ℝ) (x : EuclideanSpace ℝ (Fin p)) : ℝ :=
  τ * f x - (1 - τ) * ⟪ξ, x⟫

end HomotopyProxVM



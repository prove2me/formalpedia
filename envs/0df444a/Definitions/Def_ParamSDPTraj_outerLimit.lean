-- Prove2me | Definitions.Def_ParamSDPTraj_outerLimit
-- name    : ParamSDPTraj_outerLimit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:11:44.545277+00:00
-- url     : https://prove2.me/theorems/66319860-3028-4706-a4d7-87253ab9e5b5
-- title:
--   Outer limit of a set-valued map
-- statement:
--   Given $F:T\rightrightarrows X$, its **outer limit** at $\hat t$ is the set of $\hat x$ for which there exist $\{t_k\}\subseteq T$ with $t_k\to\hat t$ and $\{x_k\}$ with $x_k\to\hat x$ and $x_k\in F(t_k)$:
--
--   $$\limsup_{t\to\hat t}F(t)=\{\hat x\mid \exists\{t_k\}\subseteq T,\ t_k\to\hat t,\ \exists\{x_k\},\ x_k\to\hat x,\ x_k\in F(t_k)\}.$$
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, Definition 2.11, p.7

import Mathlib

namespace ParamSDPTraj

/-- **Outer limit of a set-valued map.**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, Definition 2.11, p.7: "lim sup_{t→t̂} F(t) := {x̂ | ∃{tk} ⊆ T such that tk → t̂, ∃{xk} ⊆ X,
xk → x̂ and xk ∈ F(tk)}". -/
def outerLimit {E : Type*} [TopologicalSpace E] (T : Set ℝ) (F : ℝ → Set E) (that : ℝ) : Set E :=
  {xhat | ∃ (s : ℕ → ℝ) (x : ℕ → E), (∀ k, s k ∈ T) ∧
    Filter.Tendsto s Filter.atTop (nhds that) ∧ Filter.Tendsto x Filter.atTop (nhds xhat) ∧
    ∀ k, x k ∈ F (s k)}

end ParamSDPTraj



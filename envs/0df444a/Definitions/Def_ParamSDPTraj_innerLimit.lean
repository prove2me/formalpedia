-- Prove2me | Definitions.Def_ParamSDPTraj_innerLimit
-- name    : ParamSDPTraj_innerLimit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:11:48.703994+00:00
-- url     : https://prove2.me/theorems/b10ba878-1f85-480f-bc30-a592057ba0c0
-- title:
--   Inner limit of a set-valued map
-- statement:
--   Given $F:T\rightrightarrows X$, its **inner limit** at $\hat t$ is the set of $\hat x$ such that every sequence $\{t_k\}\subseteq T$ with $t_k\to\hat t$ admits a sequence $\{x_k\}\subseteq X$ with $x_k\to\hat x$ and $x_k\in F(t_k)$:
--
--   $$\liminf_{t\to\hat t}F(t)=\{\hat x\mid \forall\{t_k\}\subseteq T,\ t_k\to\hat t,\ \exists\{x_k\},\ x_k\to\hat x,\ x_k\in F(t_k)\}.$$
--
--   **Formalization Note** The membership holds for all $k$, as printed. For a map with non-empty values on $T$ this is the same as for all large $k$.
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, Definition 2.11, p.7

import Mathlib

namespace ParamSDPTraj

/-- **Inner limit of a set-valued map.**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, Definition 2.11, p.7: "lim inf_{t→t̂} F(t) := {x̂ | ∀{tk} ⊆ T such that tk → t̂, ∃{xk} ⊆ X,
xk → x̂ and xk ∈ F(tk)}".

**Formalization Note** Sequences of times lie in `T`, as printed, and `x k ∈ F (s k)` holds for
all k, as printed. For a map with non-empty values on T (Def 2.10) this is equivalent to
"for all large k". -/
def innerLimit {E : Type*} [TopologicalSpace E] (T : Set ℝ) (F : ℝ → Set E) (that : ℝ) : Set E :=
  {xhat | ∀ s : ℕ → ℝ, (∀ k, s k ∈ T) → Filter.Tendsto s Filter.atTop (nhds that) →
    ∃ x : ℕ → E, Filter.Tendsto x Filter.atTop (nhds xhat) ∧ ∀ k, x k ∈ F (s k)}

end ParamSDPTraj



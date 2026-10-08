-- Prove2me | Definitions.Def_GeometryOfGraphs_FlowCut_Maxflow
-- name    : GeometryOfGraphs_FlowCut_Maxflow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T14:43:01.132161+00:00
-- url     : https://prove2.me/theorems/70d71e0d-c72a-4f9e-b7b5-060b9594b1dd
-- title:
--   Feasible concurrent multicommodity flow and maxflow (Section 4, p. 226)
-- statement:
--   Let $N$ be a multicommodity flow network on $V$ with capacities $C$ and commodities $(s_\mu, t_\mu, D_\mu)_{\mu=1}^k$. A **feasible concurrent flow of value** $\lambda$ is a family of arc flows $f_\mu(i,j) \ge 0$ (the amount of commodity $\mu$ sent from $i$ to $j$) such that
--
--   1. *conservation of matter*: for every commodity $\mu$ and vertex $v$,
--   $$\sum_{j} f_\mu(v,j) - \sum_j f_\mu(j,v) = \lambda D_\mu\bigl([v = s_\mu] - [v = t_\mu]\bigr),$$
--   so that $\lambda D_\mu$ units of commodity $\mu$ leave $s_\mu$ and arrive at $t_\mu$;
--   2. *joint capacity*: for every pair $i, j$, the total flow of all commodities through the undirected edge $\{i,j\}$, in both directions, is at most its capacity:
--   $$\sum_{\mu=1}^k \bigl(f_\mu(i,j) + f_\mu(j,i)\bigr) \le C_{i,j}.$$
--
--   The **maxflow** of $N$ is the largest $\lambda$ for which it is possible to flow simultaneously $\lambda D_\mu$ between $s_\mu$ and $t_\mu$ for all $\mu$:
--   $$\mathrm{maxflow}(N) = \sup\{\lambda \ge 0 : \text{there is a feasible concurrent flow of value } \lambda\}.$$
--
--   This is the version of the maximum multicommodity flow problem that Linial, London and Rabinovich study in Section 4 (the *concurrent* flow problem). Every cut gives the upper bound $\lambda\,\mathrm{Dem}(S) \le \mathrm{Cap}(S)$, so the supremum is finite as soon as some commodity has positive demand and distinct endpoints.
--
--   **Formalization Note** The flow is in arc (node–arc) form, the standard reading of "flows have to satisfy conservation of matter"; a path-flow formulation gives the same maxflow. The capacity constraint is imposed for every ordered pair $(i,j)$, which for symmetric $C$ is one constraint per edge and, since $C_{i,i} = 0$, forces loops to carry no flow. A pair with $s_\mu = t_\mu$ has zero net flow everywhere. Lean's `sSup` of an unbounded set is $0$; this only happens when no commodity has positive demand and distinct endpoints, which every theorem of the mission excludes where it matters. The value $\lambda = 0$ is always feasible (the zero flow), so the set is nonempty.
-- source:
--   N. Linial, E. London, Y. Rabinovich, The geometry of graphs and some of its algorithmic applications, Combinatorica 15 (1995), p. 226, Section 4, first paragraph

import Mathlib
import Definitions.Def_GeometryOfGraphs_FlowCut_Network

set_option autoImplicit false

namespace GeometryOfGraphs.FlowCut

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A feasible concurrent multicommodity flow of value `lam` (Linial–London–Rabinovich,
Combinatorica 15 (1995), §4, p. 226), in arc form: `f μ i j ≥ 0` is the amount of commodity `μ`
sent from `i` to `j`;
* conservation of matter: the net outflow of commodity `μ` at `v` is `lam * D μ` at `s μ`,
  `-(lam * D μ)` at `t μ`, and `0` elsewhere (and `0` everywhere if `s μ = t μ`);
* joint capacity: the total flow of all commodities, in both directions, through the undirected
  edge `{i, j}` is at most `C i j`. -/
def Network.IsFeasibleFlow (N : Network V) (f : Fin N.k → V → V → ℝ) (lam : ℝ) : Prop :=
  (∀ μ i j, 0 ≤ f μ i j) ∧
  (∀ μ v, ∑ j, f μ v j - ∑ j, f μ j v =
      lam * N.D μ * ((if v = N.s μ then 1 else 0) - (if v = N.t μ then 1 else 0))) ∧
  (∀ i j, ∑ μ, (f μ i j + f μ j i) ≤ N.C i j)

/-- `maxflow`: the largest `λ ≥ 0` for which it is possible to flow simultaneously `λ D μ` between
`s μ` and `t μ` for all `μ`, i.e. the supremum of the values of feasible concurrent flows.
(Lean's `sSup` is `0` on an unbounded set; the set is bounded when some `μ` has `D μ > 0` and
`s μ ≠ t μ`.) -/
noncomputable def Network.maxflow (N : Network V) : ℝ :=
  sSup {lam : ℝ | 0 ≤ lam ∧ ∃ f : Fin N.k → V → V → ℝ, N.IsFeasibleFlow f lam}

end GeometryOfGraphs.FlowCut



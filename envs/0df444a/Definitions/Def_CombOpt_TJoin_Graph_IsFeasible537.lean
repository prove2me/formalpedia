-- Prove2me | Definitions.Def_CombOpt_TJoin_Graph_IsFeasible537
-- name    : CombOpt_TJoin_Graph_IsFeasible537
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:05:18.490394+00:00
-- url     : https://prove2.me/theorems/436ea035-d22d-4343-9ae9-189068ff43f7
-- title:
--   Feasible solutions of the LP (5.37)
-- statement:
--   A vector $x\in\mathbb R^E$ is feasible for the linear program
--
--   $$\begin{aligned}\text{minimize } &\sum_{e\in E}c_ex_e\\ \text{subject to } & x(\delta(S)\setminus F)-x(F)\ge1-|F| \text{ for all } S\subseteq V \text{ and } F\subseteq\delta(S) \text{ such that } |F|+|S\cap T| \text{ is odd},\\ & 0\le x_e\le1 \text{ for all } e\in E\end{aligned}\tag{5.37}$$
--
--   if it satisfies these constraints. Every characteristic vector of a $T$-join is feasible.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.4, (5.37), p. 180 (PDF p. 188)

import Mathlib
import Definitions.Def_CombOpt_TJoin_Graph
import Definitions.Def_CombOpt_TJoin_Graph_cut

namespace CombOpt.TJoin

/-- **Feasible solutions of the linear program (5.37).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.4, p. 180 (PDF p. 188): "Minimize ∑(c_e x_e : e ∈ E) (5.37) subject to
x(δ(S)\F) − x(F) ≥ 1 − |F| for all S ⊆ V and F ⊆ δ(S) such that |F| + |S ∩ T| is odd;
0 ≤ x_e ≤ 1 for all e ∈ E."

`G.IsFeasible537 T x` holds when, for every node set `S` and every `F ⊆ δ(S)` with
`|F| + |S ∩ T|` odd, `∑_{e ∈ δ(S) \ F} x_e − ∑_{e ∈ F} x_e ≥ 1 − |F|`, and `0 ≤ x_e ≤ 1` for
every edge. -/
def Graph.IsFeasible537 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (T : Finset V) (x : E → ℝ) : Prop :=
  (∀ (S : Finset V) (F : Finset E), F ⊆ G.cut S → Odd (F.card + (S ∩ T).card) →
      1 - (F.card : ℝ) ≤ ∑ e ∈ G.cut S \ F, x e - ∑ e ∈ F, x e) ∧
    ∀ e, 0 ≤ x e ∧ x e ≤ 1

end CombOpt.TJoin



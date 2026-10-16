-- Prove2me | Definitions.Def_CompetitiveChores_IndivisibleRounding_Graphs
-- name    : CompetitiveChores_IndivisibleRounding_Graphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T10:58:14.284996+00:00
-- url     : https://prove2.me/theorems/54445477-8b9e-4835-9357-20eb2f1de549
-- title:
--   pp. 15–16, 37 — consumption graph, paths and simple cycles, acyclic bipartite graphs
-- statement:
--   Bipartite graphs on agents and chores (pp. 15–16, 37).
--
--   A bipartite graph on $([n],[m])$ is a set $G$ of edges $(i,j)$ between agents and chores. The **consumption graph** $G_z$ of an allocation $z$ has an edge $(i,j)$ exactly when $z_{i,j}>0$.
--
--   A **path** is an alternating sequence
--
--   $$P=(i_1,j_1,i_2,j_2,\dots,i_L,j_L,i_{L+1})$$
--
--   of agents and chores; it is a path of $G$ if both edges $(i_k,j_k)$ and $(i_{k+1},j_k)$ belong to $G$ for each $k$. It is a **cycle** if $i_{L+1}=i_1$, and a **simple cycle** if moreover the agents $i_1,\dots,i_L$ are distinct and the chores $j_1,\dots,j_L$ are distinct. The graph $G$ is **acyclic** if it contains no simple cycle with $L\ge 2$ (that is, no cycle of the bipartite graph).
--
--   Acyclicity of the consumption graph is the input condition of the rounding procedure (Algorithm 3) behind Theorem 35.
--
--   **Formalization Note** Agents and chores are 0-based (`Fin n`, `Fin m`); a path is a record with its length $L$, an agent map on `Fin (L+1)` and a chore map on `Fin L`; graphs are `Finset (Fin n × Fin m)`. Cycles with $L=1$ (going back and forth along one edge) are not cycles of a bipartite graph and are excluded by $L\ge 2$.
-- source:
--   Brânzei and Sandomirskiy, Algorithms for Competitive Division of Chores, arXiv:1907.01766v2, p. 15 (§2.4, consumption graph), p. 16 (paths and cycles, (1)), pp. 37–38 (acyclic consumption graph, proof of Theorem 35)

import Mathlib
import Definitions.Def_CompetitiveChores_IndivisibleRounding_Setting
import Definitions.Def_CompetitiveChores_RichFamily_Graphs

namespace CompetitiveChores.IndivisibleRounding

open Classical

variable {n m : ℕ}

/-- (1), p. 16: a path `P = (i_1, j_1, i_2, j_2, …, i_L, j_L, i_{L+1})` alternating between agents and
chores; `agent k` is `i_{k+1}` and `chore k` is `j_{k+1}` (0-based). -/
structure BPath (n m : ℕ) where
  /-- the number `L` of chores on the path -/
  L : ℕ
  /-- the agents `i_1, …, i_{L+1}` -/
  agent : Fin (L + 1) → Fin n
  /-- the chores `j_1, …, j_L` -/
  chore : Fin L → Fin m

/-- p. 16: a path is a cycle if `i_{L+1} = i_1`. -/
def BPath.IsCycle (P : BPath n m) : Prop :=
  P.agent (Fin.last P.L) = P.agent 0

/-- p. 16: a cycle is simple if no agent `i_k` (`k = 1, …, L`) and no chore `j_k` enters it twice. -/
def BPath.IsSimpleCycle (P : BPath n m) : Prop :=
  P.IsCycle ∧ (fun k : Fin P.L => P.agent k.castSucc).Injective ∧ P.chore.Injective

/-- A path of the graph `G`: for each `k`, both edges `(i_k, j_k)` and `(i_{k+1}, j_k)` are in `G`. -/
def BPath.InGraph (G : Finset (Fin n × Fin m)) (P : BPath n m) : Prop :=
  ∀ k, (P.agent k.castSucc, P.chore k) ∈ G ∧ (P.agent k.succ, P.chore k) ∈ G

/-- pp. 37–38: the bipartite graph `G` is acyclic if it contains no simple cycle
`(i_1, j_1, i_2, …, j_L, i_1)` with `L ≥ 2` agents. -/
def IsAcyclic (G : Finset (Fin n × Fin m)) : Prop :=
  ¬ ∃ C : BPath n m, 2 ≤ C.L ∧ C.IsSimpleCycle ∧ C.InGraph G

end CompetitiveChores.IndivisibleRounding



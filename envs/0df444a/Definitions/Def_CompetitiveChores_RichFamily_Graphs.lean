-- Prove2me | Definitions.Def_CompetitiveChores_RichFamily_Graphs
-- name    : CompetitiveChores_RichFamily_Graphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:40.504807+00:00
-- url     : https://prove2.me/theorems/4d83112a-d7fc-4b5e-a9ef-d8ae6537e635
-- title:
--   pp. 15–16, 23, 29 — consumption graphs, MWW graphs (Definition 12), rich families (Definition 11), paths and π(P) (1), trading cycles, transposition, components and equal split (3)
-- statement:
--   This file adds the combinatorial objects of Brânzei and Sandomirskiy's enumeration of competitive utility profiles: bipartite graphs on agents $[n]$ and chores $[m]$, represented by their sets of edges $(i,j)$.
--
--   1. **Consumption graph (p. 15).** The consumption graph $G_z$ of an allocation $z$ links agent $i$ and chore $j$ iff $z_{i,j}>0$.
--   2. **MWW graph (Definition 12).** For weights $\tau\in\mathbb R^n_{>0}$, the *maximal weighted welfare graph* $G_\tau(v)$ links agent $i$ and chore $j$ iff
--   $$\tau_i\,|v_{i,j}|\le\tau_{i'}\,|v_{i',j}|\qquad\text{for each agent } i'\in[n],$$
--   i.e. each chore is linked to all agents of minimal weighted disutility. A graph has *no lonely agents* if every agent is linked to at least one chore; $\mathrm{MWW}_{non\text{-}lonely}(v)$ is the set of MWW graphs ($\tau\in\mathbb R^n_{>0}$) with no lonely agents.
--   3. **Rich family (Definition 11).** A collection of bipartite graphs is *rich* for $v$ if for every Pareto optimal utility profile $u\in\mathcal U^*(v)\cap\mathbb R^n_{<0}$ there is a feasible allocation $z$ with $u(z)=u$ whose consumption graph $G_z$ belongs to the collection.
--   4. **Transposition (p. 23).** $v^T$ is the problem in which agents and chores switch roles ($m$ agents, $n$ chores), and a graph on $([n],[m])$ is identified with the graph on $([m],[n])$ having the same edges.
--   5. **Paths, cycles, $\pi$ (formula (1), p. 16).** A path is $\mathcal P=(i_1,j_1,i_2,j_2,\dots,i_L,j_L,i_{L+1})$ with agents $i_k$ and chores $j_k$; the product of disutilities along it is
--   $$\pi(\mathcal P)=\prod_{k=1}^{L}\frac{|v_{i_k,j_k}|}{|v_{i_{k+1},j_k}|}.$$
--   It is a *cycle* if $i_{L+1}=i_1$, and a cycle is *simple* if no agent $i_k$ and no chore $j_k$ ($1\le k\le L$) occurs twice. A cycle with $L\ge2$ is a *profitable trading cycle* for an allocation $z$ if $z_{i_k,j_k}>0$ for $k=1,\dots,L$ and $\pi(\mathcal C)>1$. A path *of a graph* $G$ uses only edges of $G$: $(i_k,j_k)$ and $(i_{k+1},j_k)$ are edges for every $k$.
--   6. **Components and equal split ((3), p. 29).** $N_i$ is the set of agents in the connected component of agent $i$ in $G$ (including $i$), i.e. the agents reachable from $i$ by a path of $G$. $\bar z$ is the allocation in which each chore is divided equally among the agents linked to it in $G$, and $\bar u=u(\bar z)$.
--
--   These objects carry the paper's reduction of the competitive rule to a finite enumeration: MWW graphs describe the faces of the Pareto frontier, and a competitive utility profile is recovered from its consumption graph through $\pi$ and $\bar u$.
--
--   **Formalization Note** A graph is a `Finset (Fin n × Fin m)` of edges. A path is a record with its length $L$, its $L+1$ agents and its $L$ chores (0-based). The length $L=0$ is allowed: it is the trivial path $(i)$ with $\pi=1$, the convention $\pi(\mathcal P_{i,i})=1$ of p. 29; formula (1) itself is for $L\ge1$, and the theorems that need $L\ge1$ or $L\ge2$ say so. The equal split $\bar z$ gives a chore with no neighbour in $G$ to nobody; it is used only for graphs without isolated nodes. The transposition of graphs is the map swapping the two ends of every edge.
-- source:
--   Brânzei and Sandomirskiy, Algorithms for Competitive Division of Chores, arXiv:1907.01766v2, p. 15 (§2.4, consumption graph, Definition 11, Definition 12, no lonely agents), p. 16 (§2.5, formula (1), cycles, profitable trading cycles), p. 23 (transposition), p. 29 (N_i, P_{i,i'}, (3))

import Mathlib
import Definitions.Def_CompetitiveChores_RichFamily_Setting

namespace CompetitiveChores.RichFamily

open Classical

variable {n m : ℕ}

/-- §2.4, p. 15: the consumption graph `G_z` of an allocation `z`, the bipartite graph on agents and
chores (as a set of edges `(i, j)`) with an edge exactly when `z_{i,j} > 0`. -/
noncomputable def consumptionGraph (z : Fin n → Fin m → ℝ) : Finset (Fin n × Fin m) :=
  Finset.univ.filter (fun e => 0 < z e.1 e.2)

/-- Definition 12, p. 15: the maximal weighted welfare (MWW) graph `G_τ(v)`: agent `i` and chore `j`
are linked if `τ_i |v_{i,j}| ≤ τ_{i'} |v_{i',j}|` for each agent `i'`. -/
noncomputable def mwwGraph (v : Fin n → Fin m → ℝ) (τ : Fin n → ℝ) : Finset (Fin n × Fin m) :=
  Finset.univ.filter (fun e => ∀ i', τ e.1 * |v e.1 e.2| ≤ τ i' * |v i' e.2|)

/-- p. 15: a bipartite graph has no lonely agents if each agent is connected to at least one chore. -/
def NoLonelyAgents (G : Finset (Fin n × Fin m)) : Prop :=
  ∀ i, ∃ j, (i, j) ∈ G

/-- p. 15: the set of all MWW graphs `G_τ(v)`, `τ ∈ ℝ^n_{>0}`. -/
def mwwGraphs (v : Fin n → Fin m → ℝ) : Set (Finset (Fin n × Fin m)) :=
  {G | ∃ τ : Fin n → ℝ, (∀ i, 0 < τ i) ∧ G = mwwGraph v τ}

/-- p. 15: `MWW_{non-lonely}(v)`, the MWW graphs with no lonely agents. -/
def mwwNonLonely (v : Fin n → Fin m → ℝ) : Set (Finset (Fin n × Fin m)) :=
  {G | G ∈ mwwGraphs v ∧ NoLonelyAgents G}

/-- Definition 11, p. 15: a collection of bipartite graphs is rich for `v` if for every Pareto-optimal
utility profile `u ∈ ℝ^n_{<0}` there is a feasible allocation `z` with `u(z) = u` whose consumption
graph belongs to the collection. -/
def IsRich (v : Fin n → Fin m → ℝ) (𝒢 : Set (Finset (Fin n × Fin m))) : Prop :=
  ∀ u ∈ paretoFrontier v, (∀ i, u i < 0) →
    ∃ z, IsFeasible z ∧ utilityProfile v z = u ∧ consumptionGraph z ∈ 𝒢

/-- p. 23: the transposed matrix `v^T`, in which agents and chores switch roles. -/
def transposeValues (v : Fin n → Fin m → ℝ) : Fin m → Fin n → ℝ :=
  fun j i => v i j

/-- p. 23: the natural bijection from bipartite graphs on `([n], [m])` to bipartite graphs on
`([m], [n])`, swapping the two ends of every edge. -/
def transposeGraph (G : Finset (Fin n × Fin m)) : Finset (Fin m × Fin n) :=
  G.map (Equiv.prodComm (Fin n) (Fin m)).toEmbedding

/-- (1), p. 16: a path `P = (i_1, j_1, i_2, j_2, …, i_L, j_L, i_{L+1})` alternating between agents and
chores; `agent k` is `i_{k+1}` and `chore k` is `j_{k+1}` (0-based). The length `L = 0` is allowed and
is the trivial path `(i_1)` of the convention `π(P_{i,i}) = 1` (p. 29). -/
structure BPath (n m : ℕ) where
  /-- the number `L` of chores on the path -/
  L : ℕ
  /-- the agents `i_1, …, i_{L+1}` -/
  agent : Fin (L + 1) → Fin n
  /-- the chores `j_1, …, j_L` -/
  chore : Fin L → Fin m

/-- (1), p. 16: the product of disutilities along the path,
`π(P) = ∏_{k=1}^{L} |v_{i_k, j_k}| / |v_{i_{k+1}, j_k}|` (the empty product `1` when `L = 0`). -/
noncomputable def pathProd (v : Fin n → Fin m → ℝ) (P : BPath n m) : ℝ :=
  ∏ k : Fin P.L, |v (P.agent k.castSucc) (P.chore k)| / |v (P.agent k.succ) (P.chore k)|

/-- p. 16: a path is a cycle if `i_{L+1} = i_1`. -/
def BPath.IsCycle (P : BPath n m) : Prop :=
  P.agent (Fin.last P.L) = P.agent 0

/-- p. 16: a cycle is simple if no agent `i_k` (`k = 1, …, L`) and no chore `j_k` enters it twice. -/
def BPath.IsSimpleCycle (P : BPath n m) : Prop :=
  P.IsCycle ∧ (fun k : Fin P.L => P.agent k.castSucc).Injective ∧ P.chore.Injective

/-- p. 16: a cycle `C = (i_1, j_1, …, i_{L+1} = i_1)` with `L ≥ 2` in which each agent `i_k` consumes some
of chore `j_k` (`z_{i_k, j_k} > 0`) is a profitable trading cycle for `z` if `π(C) > 1`. -/
def IsProfitableTradingCycle (v : Fin n → Fin m → ℝ) (z : Fin n → Fin m → ℝ) (C : BPath n m) :
    Prop :=
  2 ≤ C.L ∧ C.IsCycle ∧ (∀ k, 0 < z (C.agent k.castSucc) (C.chore k)) ∧ 1 < pathProd v C

/-- A path of the graph `G`: for each `k`, both edges `(i_k, j_k)` and `(i_{k+1}, j_k)` are in `G`. -/
def BPath.InGraph (G : Finset (Fin n × Fin m)) (P : BPath n m) : Prop :=
  ∀ k, (P.agent k.castSucc, P.chore k) ∈ G ∧ (P.agent k.succ, P.chore k) ∈ G

/-- p. 29: `N_i`, the agents of the connected component of agent `i` in `G` (including `i`): the agents
`i'` reachable from `i` by a path of `G`. -/
noncomputable def component (G : Finset (Fin n × Fin m)) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun i' => ∃ P : BPath n m, P.InGraph G ∧ P.agent 0 = i ∧
    P.agent (Fin.last P.L) = i')

/-- (3), p. 29: `z̄`, the allocation in which each chore is divided equally among the agents connected
to it in `G`. -/
noncomputable def equalSplit (G : Finset (Fin n × Fin m)) : Fin n → Fin m → ℝ :=
  fun i j => if (i, j) ∈ G then 1 / ((Finset.univ.filter (fun i' => (i', j) ∈ G)).card : ℝ) else 0

end CompetitiveChores.RichFamily



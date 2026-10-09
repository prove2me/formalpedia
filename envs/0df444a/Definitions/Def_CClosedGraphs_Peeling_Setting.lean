-- Prove2me | Definitions.Def_CClosedGraphs_Peeling_Setting
-- name    : CClosedGraphs_Peeling_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T20:19:48.85498+00:00
-- url     : https://prove2.me/theorems/7a934df1-2548-4f2c-9509-80b8f2f7b663
-- title:
--   Definitions 1.1–1.3, pp. 2–3 — c-closed graphs, bad pairs, weakly c-closed graphs and the number of maximal cliques
-- statement:
--   All graphs are finite, simple and undirected. For a graph $G=(V,E)$ and a vertex $v$, $N(v)$ is the neighbourhood of $v$; for $W\subseteq V$, $G[W]$ is the subgraph induced by $W$. The common neighbours of $u$ and $v$ are the vertices of $N(u)\cap N(v)$.
--
--   1. **$c$-closed graph** (Definition 1.1). For a positive integer $c$, $G$ is *$c$-closed* if any two distinct vertices $u,v$ with at least $c$ common neighbours are adjacent:
--   $$u\neq v,\ |N(u)\cap N(v)|\ge c \ \Longrightarrow\ \{u,v\}\in E.$$
--   2. **Bad pair** (Definition 1.2). Given $c$, a *bad pair* of the induced subgraph $G[W]$ is a pair of distinct, non-adjacent vertices $u,v\in W$ with at least $c$ common neighbours inside $W$, i.e. $|W\cap N(u)\cap N(v)|\ge c$.
--   3. **Weakly $c$-closed graph** (Definition 1.3). A graph on the vertex set $\{0,\dots,n-1\}$ is *weakly $c$-closed* if there is an ordering $v_1,\dots,v_n$ of its vertices such that for every $i$, the vertex $v_i$ is in no bad pair of the graph induced by $\{v_i,v_{i+1},\dots,v_n\}$.
--   4. **Maximal cliques.** A *clique* is a set of pairwise adjacent vertices; a clique $K\subseteq W$ is a *maximal clique of $G[W]$* if no clique $T$ with $K\subsetneq T\subseteq W$ exists. We write $\mathrm{mc}(G[W])$ for the number of maximal cliques of $G[W]$ and $\mathrm{mc}(G)=\mathrm{mc}(G[V])$.
--
--   Every $c$-closed graph is weakly $c$-closed (take any ordering: common neighbours inside a subset are fewer). The paper's $F(n,c)$, the maximum number of maximal cliques of a $c$-closed graph on $n$ vertices, is the largest value of $\mathrm{mc}(G)$ over such graphs; the theorems of this mission bound $\mathrm{mc}(G)$ for every graph in the class, which is the same content.
--
--   **Formalization Note** The vertex type is an arbitrary finite type with decidable equality; the weakly closed notion is stated for $G$ on `Fin n`, the ordering being a permutation $\sigma$ with $v_i=\sigma(i)$ and $\{v_i,\dots,v_n\}=\{x : i\le\sigma^{-1}(x)\}$. Common-neighbour counts are `Set.ncard`, which is the true cardinality since the vertex type is finite. "At least $c$" is $c\le|\cdot|$. Maximal cliques of $G[W]$ are counted as finite vertex sets of the ambient type ($K\subseteq W$, maximal among cliques contained in $W$), so `numMaxCliquesIn G W` is the number of maximal cliques of the induced graph $G[W]$; the empty set is the unique maximal clique of the empty graph.
-- source:
--   Fox, Roughgarden, Seshadhri, Wei and Wein, Finding cliques in social networks: a new distribution-free model, arXiv:1804.07431v1, pp. 2–3, Definitions 1.1–1.3 and the definition of maximal clique (§1.3, p. 3); §1.6 Notation, p. 6

import Mathlib

namespace CClosedGraphs.Peeling

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Definition 1.1 (p. 2): `G` is `c`-closed if any two distinct vertices with at least `c`
common neighbours are adjacent. -/
def IsCClosed (c : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ u v : V, u ≠ v → c ≤ (G.commonNeighbors u v).ncard → G.Adj u v

/-- Definition 1.2 (p. 3): `{u, v}` is a bad pair of the induced subgraph `G[W]`: both lie in
`W`, they are distinct and non-adjacent, and they have at least `c` common neighbours inside
`W`. -/
def IsBadPairIn (c : ℕ) (G : SimpleGraph V) (W : Set V) (u v : V) : Prop :=
  u ∈ W ∧ v ∈ W ∧ u ≠ v ∧ ¬ G.Adj u v ∧ c ≤ (W ∩ G.commonNeighbors u v).ncard

/-- Definition 1.3 (p. 3): there is an ordering `v_i = σ i` of the vertices such that, for
every `i`, `v_i` is in no bad pair of the subgraph induced by `{v_i, v_{i+1}, …, v_n}`
(`= {x | i ≤ σ⁻¹ x}`). -/
def IsWeaklyCClosed {n : ℕ} (c : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin n, ∀ w : Fin n,
    ¬ IsBadPairIn c G {x | i ≤ σ.symm x} (σ i) w

open Classical in
/-- The maximal cliques of the induced subgraph `G[W]`, as vertex sets of `V`: the vertex sets
`K ⊆ W` that are cliques of `G` and are not properly contained in another such set. -/
noncomputable def maxCliquesIn (G : SimpleGraph V) (W : Set V) : Finset (Finset V) :=
  Finset.univ.filter fun K =>
    Maximal (fun T : Finset V => (↑T : Set V) ⊆ W ∧ G.IsClique (↑T : Set V)) K

/-- The number of maximal cliques of the induced subgraph `G[W]`. -/
noncomputable def numMaxCliquesIn (G : SimpleGraph V) (W : Set V) : ℕ := #(maxCliquesIn G W)

/-- The number of maximal cliques of `G`. -/
noncomputable def numMaxCliques (G : SimpleGraph V) : ℕ := numMaxCliquesIn G Set.univ

end CClosedGraphs.Peeling



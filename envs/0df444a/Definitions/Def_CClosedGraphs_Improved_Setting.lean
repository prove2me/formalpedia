-- Prove2me | Definitions.Def_CClosedGraphs_Improved_Setting
-- name    : CClosedGraphs_Improved_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:21:32.137679+00:00
-- url     : https://prove2.me/theorems/31f6664e-3e1b-4990-8af0-9d99a77cae17
-- title:
--   §1.2 and §3, pp. 3–10 — relative c-closedness, N(S), N₂(v) and F₀
-- statement:
--   All graphs are finite, simple and undirected. For a graph $G=(V,E)$ and a vertex $x$, write $N(x)$ for the set of neighbours of $x$; for a vertex set $W\subseteq V$, $G[W]$ is the subgraph induced by $W$.
--
--   1. **$c$-closed graphs** (Definition 1.1). For a positive integer $c$, $G$ is *$c$-closed* if, whenever two distinct vertices $u,v\in V$ have at least $c$ common neighbours, $(u,v)$ is an edge of $G$. The relative version says that $G[W]$ is $c$-closed: any two distinct vertices $u,v\in W$ with $|W\cap N(u)\cap N(v)|\ge c$ are adjacent.
--   2. **Maximal cliques.** A clique of $G[W]$ is a set $K\subseteq W$ of pairwise adjacent vertices; it is *maximal* if no vertex of $W$ can be added to it. We write $\mathrm{mc}(G[W])$ for the number of maximal cliques of $G[W]$ and $\mathrm{mc}(G)=\mathrm{mc}(G[V])$. The paper's $F(n,c)$ is the largest value of $\mathrm{mc}(G)$ over $c$-closed graphs on $n$ vertices.
--   3. **Common neighbourhood of a set** (p. 9). For a set $S$ of vertices, $N(S)=\bigcap_{u\in S}N(u)$.
--   4. **Second neighbourhood** (p. 9). $N_2(v)$ is the set of vertices at distance exactly $2$ from $v$; computed in $G[W]$, it is the set of $x\in W$ with $x\ne v$, $x$ not adjacent to $v$, and $x$ adjacent to some neighbour of $v$ lying in $W$.
--   5. **The bound function** (p. 10). For a real $m\ge 0$ and a positive integer $c$,
--   $$F_0(m,c)=4^{(c+4)(c-1)/2}\,m^{\,2-2^{1-c}}.$$
--
--   These are the objects in which Theorem 3.1 and the steps of its proof are stated.
--
--   **Formalization Note** Vertices form a finite type with decidable equality. Common-neighbour counts are `Set.ncard`, the true cardinality on a finite type. Maximal cliques are counted as finite vertex sets $K\subseteq W$ that are maximal (under inclusion) among cliques contained in $W$, so the empty graph has exactly one maximal clique, the empty set. "At least $c$" is `c ≤ ncard`. Powers in $F_0$ are real powers. The c-closedness and maximal-clique definitions used here come from the reviewed shared module `CClosedGraphs.Peeling.Setting`; this item defines their relative and auxiliary forms.
-- source:
--   Fox, Roughgarden, Seshadhri, Wei and Wein, Finding cliques in social networks: a new distribution-free model, arXiv:1804.07431v1, p. 2, Definition 1.1; p. 3 (maximal clique); p. 9 (N(S), N_2(v)); p. 10 (F_0)

import Mathlib
import Definitions.Def_CClosedGraphs_Peeling_Setting

namespace CClosedGraphs.Improved

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The induced subgraph `G[W]` is `c`-closed: two distinct vertices of `W` with at least `c`
common neighbours inside `W` are adjacent. -/
def IsCClosedOn (c : ℕ) (G : SimpleGraph V) (W : Set V) : Prop :=
  ∀ u ∈ W, ∀ v ∈ W, u ≠ v → c ≤ (W ∩ G.commonNeighbors u v).ncard → G.Adj u v

open Classical in

/-- `N(S) = ⋂_{u ∈ S} N(u)`: the vertices adjacent to every vertex of `S` (p. 9). -/
def commonNbrs (G : SimpleGraph V) (S : Finset V) : Set V := {x | ∀ u ∈ S, G.Adj u x}

/-- `N₂(v)` computed in the induced subgraph `G[W]`: the vertices of `W` at distance exactly 2
from `v` in `G[W]`, i.e. different from `v`, not adjacent to `v`, and adjacent to some
neighbour of `v` lying in `W` (p. 9). -/
def dist2In (G : SimpleGraph V) (W : Set V) (v : V) : Set V :=
  {x | x ∈ W ∧ x ≠ v ∧ ¬ G.Adj v x ∧ ∃ y ∈ W, G.Adj v y ∧ G.Adj y x}

/-- `F₀(m, c) = 4^{(c+4)(c−1)/2} m^{2 − 2^{1−c}}` (p. 10), with real exponents. -/
noncomputable def F0 (m : ℝ) (c : ℕ) : ℝ :=
  (4 : ℝ) ^ (((c : ℝ) + 4) * ((c : ℝ) - 1) / 2) * m ^ ((2 : ℝ) - (2 : ℝ) ^ (1 - (c : ℝ)))

end CClosedGraphs.Improved



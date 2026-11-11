-- Prove2me | Definitions.Def_IncApproxVC_Oblivious_VertexConnectivity
-- name    : IncApproxVC_Oblivious_VertexConnectivity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:42:35.128253+00:00
-- url     : https://prove2.me/theorems/f2b224a2-7567-4ab8-85a7-dbfe93e8c7a7
-- title:
--   Strong connectivity, vertex cuts, separation triples and the vertex connectivity $\kappa(G)$
-- statement:
--   Let $G=(V,E)$ be a directed graph with $n=|V|$. For $W\subseteq V$, the induced graph $G[W]$ is **strongly connected** if for all $u,v\in W$ there is a directed path from $u$ to $v$ using only vertices of $W$ (this holds vacuously when $|W|\le 1$); $G$ is strongly connected if $G[V]$ is.
--
--   A **vertex cut** is a set $S\subseteq V$ whose deletion makes $G$ no longer strongly connected, that is $G[V\setminus S]$ is not strongly connected, or that has $|S|=n-1$. The **vertex connectivity** is
--   $$\kappa(G)=\min\{|S| : S \text{ is a vertex cut of } G\}.$$
--   Every set of $n-1$ vertices is a vertex cut, so the minimum exists and $\kappa(G)\le n-1$; for the complete digraph $\kappa=n-1$, and $\kappa(G)=0$ exactly when $G$ is not strongly connected or $n=1$.
--
--   A **partition** $(L,S,R)$ of $V$ consists of three pairwise disjoint sets with union $V$ (parts may be empty). A **separation triple** is a partition with $L\ne\emptyset$, $R\ne\emptyset$ and $E_G(L,R)=\emptyset$; its size is $|S|$ and its volume $\mathrm{vol}^+_G(L)$. It is **$s$-rooted** if $s\in L$ and an **$s$–$t$** separation triple (an $s$–$t$ vertex cut) if moreover $t\in R$.
--
--   **Formalization Note.** Paths inside $W$ are the reflexive–transitive closure of the edge relation restricted to $W$. `kappa` is the `sInf` over the sizes of vertex cuts, a nonempty set of naturals, hence a minimum. The clause "$|S|=n-1$" uses natural subtraction, which is exact for $n\ge 1$.
-- source:
--   Adena, Henzinger, Rutschmann, Incremental Approximate Vertex Connectivity via Almost-Linear Time Local Cut Algorithms, STOC 2027 submission (manuscript sha256 d6baac6b…), p. 4, §2 (Edge Connectivity and Cuts; Vertex Connectivity and Cuts)

import Mathlib
import Definitions.Def_IncApproxVC_Oblivious_Digraph

/-!
# Strong connectivity, vertex cuts, separation triples and the vertex connectivity `κ(G)`

Adena, Henzinger, Rutschmann, *Incremental Approximate Vertex Connectivity via Almost-Linear Time
Local Cut Algorithms*, STOC 2027 submission (manuscript sha256 d6baac6b…), p. 4, §2
("Edge Connectivity and Cuts", "Vertex Connectivity and Cuts").

* `StronglyConnectedOn G W`: the induced graph `G[W]` has a directed path, inside `W`, from every
  vertex of `W` to every vertex of `W` (vacuous for `|W| ≤ 1`). `IsStronglyConnected G` is the case
  `W = V`.
* `IsVertexCut G S`: "a set `S ⊆ V` whose deletion makes `G` no longer strongly connected, or that
  has `|S| = n − 1`", with `n = |V|` and `G \ S = G[V \ S]`.
* `kappa G`: the minimum size of a vertex cut. A set of size `n − 1` always exists, so the minimum
  is over a nonempty set and `κ(G) ≤ n − 1`.
* `IsPartition3 L S R`: `(L, S, R)` is a partition of `V` into three pairwise disjoint sets (empty
  parts allowed).
* `IsSeparationTriple G L S R`: a partition with `L, R ≠ ∅` and `E_G(L, R) = ∅`. Its size is `|S|`
  and its volume `vol⁺(L)`; it is `s`-rooted if `s ∈ L` and `s–t` if moreover `t ∈ R`.
-/

namespace IncApproxVC.Oblivious

namespace Digraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One step of a directed path inside `W`: an edge of `G` with both ends in `W`. -/
def stepIn (G : Digraph V) (W : Finset V) (u v : V) : Prop :=
  u ∈ W ∧ v ∈ W ∧ (u, v) ∈ G.edges

/-- The induced graph `G[W]` is strongly connected: there is a directed path inside `W` from every
vertex of `W` to every vertex of `W`. -/
def StronglyConnectedOn (G : Digraph V) (W : Finset V) : Prop :=
  ∀ u ∈ W, ∀ v ∈ W, Relation.ReflTransGen (G.stepIn W) u v

/-- `G` is strongly connected: a directed path between every ordered pair of vertices. -/
def IsStronglyConnected (G : Digraph V) : Prop :=
  G.StronglyConnectedOn Finset.univ

/-- A vertex cut (p. 4): a set `S` whose deletion leaves a graph `G[V \ S]` that is not strongly
connected, or a set with `|S| = n − 1`. -/
def IsVertexCut (G : Digraph V) (S : Finset V) : Prop :=
  ¬ G.StronglyConnectedOn Sᶜ ∨ S.card = Fintype.card V - 1

/-- The vertex connectivity `κ(G)`: the minimum size of a vertex cut. The set of sizes is never
empty (every set of `n − 1` vertices is a vertex cut), so this `sInf` is a minimum. -/
noncomputable def kappa (G : Digraph V) : ℕ :=
  sInf {k : ℕ | ∃ S : Finset V, G.IsVertexCut S ∧ S.card = k}

/-- `(L, S, R)` is a partition of `V` into three pairwise disjoint sets (empty parts allowed). -/
def IsPartition3 (L S R : Finset V) : Prop :=
  L ∪ S ∪ R = Finset.univ ∧ Disjoint L S ∧ Disjoint L R ∧ Disjoint S R

/-- A separation triple (p. 4): a partition `(L, S, R)` of `V` with `L ≠ ∅`, `R ≠ ∅` and no edge
from `L` to `R`. -/
def IsSeparationTriple (G : Digraph V) (L S R : Finset V) : Prop :=
  IsPartition3 L S R ∧ L.Nonempty ∧ R.Nonempty ∧ G.edgesBetween L R = ∅

end Digraph

end IncApproxVC.Oblivious



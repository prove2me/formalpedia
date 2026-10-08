-- Prove2me | Definitions.Def_TreewidthApprox_Pushed_Setting
-- name    : TreewidthApprox_Pushed_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:29:44.644553+00:00
-- url     : https://prove2.me/theorems/a5eda2be-5027-4ec4-83bc-a0aee27db030
-- title:
--   pp. 320, 369 — components of G ∖ X, separations, terminal separations, left- and right-pushed (Definition 6.4)
-- statement:
--   This file fixes the combinatorial vocabulary of §6.4.3 of Bodlaender et al. Throughout, $G$ is a finite simple graph with vertex set $V(G)$, and all vertex sets are finite subsets of $V(G)$.
--
--   1. **Components of $G \setminus X$** (p. 320). For $X \subseteq V(G)$, two vertices $u, v$ are *joined avoiding $X$* if there is a walk from $u$ to $v$ in $G$ none of whose vertices, endpoints included, lies in $X$. For $u \notin X$, the set $C_X(u)$ of all vertices joined to $u$ avoiding $X$ is the vertex set of the connected component of $G \setminus X$ that contains $u$.
--   2. **Partitions.** A triple $(P_1, P_2, P_3)$ is a *partition* of a set $W$ if the three sets are pairwise disjoint and $P_1 \cup P_2 \cup P_3 = W$. Parts may be empty.
--   3. **Separations** (p. 369). A partition $(L, X, R)$ of $V(G)$ is a *separation* of $G$ if no edge of $G$ joins a vertex of $L$ to a vertex of $R$. Its *order* is $|X|$. It is *$\alpha$-balanced* if moreover $|L|, |R| \le \alpha |V(G)|$.
--   4. **Terminal separations** (Definition 6.4, p. 369). Let $W \subseteq V(G)$, let $G[W]$ be the induced subgraph, and let $T_L, T_R$ be sets of terminals. A partition $(L, X, R)$ of $W$ is a *terminal separation of $G[W]$ of order $\ell$* if
--      (i) $T_L \subseteq L$ and $T_R \subseteq R$;
--      (ii) there is no edge between $L$ and $R$;
--      (iii) $|X| \le \ell$.
--   5. **Pushed separations** (Definition 6.4). A terminal separation $(L, X, R)$ of $G[W]$ of order $\ell$ is *left-pushed* if $|L| \ge |L'|$ for every terminal separation $(L', X', R')$ of $G[W]$ of order $\ell$ (with the same $W$, $T_L$, $T_R$), and *right-pushed* if $|R| \ge |R'|$ for every such separation.
--
--   These notions turn the search for a small balanced separator into a maximization problem: Lemma 6.5 chooses terminal sets and order budgets so that gluing a left-pushed and a right-pushed terminal separation produces a balanced separation of the whole graph.
--
--   **Formalization Note** The vertex type is a finite type `V : Type` (universe 0, matching the published `RobertsonSeymour1986.GM5.TreewidthLE`), and vertex sets are `Finset V`. The induced subgraph $G[W]$ is encoded by its vertex set $W$: a terminal separation of $G[W]$ is a partition of $W$, and "no edge between $L$ and $R$" uses the adjacency of $G$ on vertices of $W$, which is the adjacency of $G[W]$. Definition 6.4 asks $T_L, T_R$ to be disjoint; this follows from (i) and the disjointness of $L$ and $R$, so it is not a separate clause. "Of order $\ell$" means $|X| \le \ell$, as in (iii), and the maximum defining pushed separations ranges over all terminal separations with $|X| \le \ell$. Balance bounds are stated in the theorem items rather than as a separate predicate here.
-- source:
--   Bodlaender, Drange, Dregi, Fomin, Lokshtanov and Pilipczuk, A c^k n 5-approximation algorithm for treewidth, SIAM J. Comput. 45(2) (2016), p. 320 (§1, components of G \ X), p. 369 (§6.4.3, α-balanced separation and order; Definition 6.4), https://doi.org/10.1137/130947374

import Mathlib

namespace TreewidthApprox.Pushed

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `u` and `v` are joined by a walk of `G` none of whose vertices (endpoints included) lies in
`X`; i.e. `u` and `v` lie in the same connected component of `G \ X` (p. 320). -/
def AvoidReach (G : SimpleGraph V) (X : Finset V) (u v : V) : Prop :=
  ∃ p : G.Walk u v, ∀ w ∈ p.support, w ∉ X

/-- For `u ∉ X`: the vertex set of the connected component of `G \ X` containing `u`. -/
noncomputable def avoidComp (G : SimpleGraph V) (X : Finset V) (u : V) : Finset V := by
  classical exact Finset.univ.filter (AvoidReach G X u)

/-- `(P₁, P₂, P₃)` is a partition of `W`: pairwise disjoint with union `W`. Parts may be empty. -/
def IsPartition3 (W P₁ P₂ P₃ : Finset V) : Prop :=
  Disjoint P₁ P₂ ∧ Disjoint P₁ P₃ ∧ Disjoint P₂ P₃ ∧ P₁ ∪ P₂ ∪ P₃ = W

/-- There is no edge of `G` between `L` and `R`. -/
def NoEdge (G : SimpleGraph V) (L R : Finset V) : Prop :=
  ∀ a ∈ L, ∀ b ∈ R, ¬ G.Adj a b

/-- p. 369: `(L, X, R)` is a separation of `G`: a partition of `V(G)` with no edge between `L`
and `R`. Its order is `|X|`. -/
def IsSeparation (G : SimpleGraph V) (L X R : Finset V) : Prop :=
  IsPartition3 Finset.univ L X R ∧ NoEdge G L R

/-- Definition 6.4, for the induced subgraph `G[W]` with terminals `TL`, `TR`: `(L, X, R)` is a
partition of `W` with `TL ⊆ L`, `TR ⊆ R`, no edge between `L` and `R`, and `|X| ≤ ℓ`
(a terminal separation of `G[W]` of order `ℓ`). -/
def IsTerminalSep (G : SimpleGraph V) (W TL TR : Finset V) (ℓ : ℕ) (L X R : Finset V) : Prop :=
  IsPartition3 W L X R ∧ TL ⊆ L ∧ TR ⊆ R ∧ NoEdge G L R ∧ X.card ≤ ℓ

/-- Definition 6.4: `(L, X, R)` is a left-pushed terminal separation of `G[W]` of order `ℓ`:
`|L|` is maximum among all terminal separations of `G[W]` of order `ℓ`. -/
def IsLeftPushed (G : SimpleGraph V) (W TL TR : Finset V) (ℓ : ℕ) (L X R : Finset V) : Prop :=
  IsTerminalSep G W TL TR ℓ L X R ∧
    ∀ L' X' R', IsTerminalSep G W TL TR ℓ L' X' R' → L'.card ≤ L.card

/-- Definition 6.4: `(L, X, R)` is a right-pushed terminal separation of `G[W]` of order `ℓ`:
`|R|` is maximum among all terminal separations of `G[W]` of order `ℓ`. -/
def IsRightPushed (G : SimpleGraph V) (W TL TR : Finset V) (ℓ : ℕ) (L X R : Finset V) : Prop :=
  IsTerminalSep G W TL TR ℓ L X R ∧
    ∀ L' X' R', IsTerminalSep G W TL TR ℓ L' X' R' → R'.card ≤ R.card

end TreewidthApprox.Pushed



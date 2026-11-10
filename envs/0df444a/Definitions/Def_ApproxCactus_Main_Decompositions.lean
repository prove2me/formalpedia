-- Prove2me | Definitions.Def_ApproxCactus_Main_Decompositions
-- name    : ApproxCactus_Main_Decompositions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:01:02.833976+00:00
-- url     : https://prove2.me/theorems/040375f4-8d29-4908-89d8-207c703e7f1d
-- title:
--   Graph-decompositions over loopless multigraphs, strong cacti, cuts, displayed separations, clique-faithfulness and ψ-isomorphism
-- statement:
--   A **graph-decomposition** of a finite graph $G$ consists of a finite loopless multigraph $H$ (nodes, edges, and for each edge its two distinct endpoints; parallel edges allowed) with a **bag** $V_h\subseteq V(G)$ at each node $h$ and a set of designated **P-nodes**, such that (H1) every vertex of $G$ lies in a bag and every edge of $G$ has both ends in a common bag, and (H2) for every vertex $v$ the nodes whose bags contain $v$ induce a connected (in particular nonempty) subgraph of $H$. The **adhesion-set** of an edge $hh'$ is $V_h\cap V_{h'}$; the **centre** is the intersection of all bags.
--
--   A **cut** of $H$ is a bipartition $(U,W)$ of its nodes (either part may be empty); $E_H(U,W)$ is the set of edges between $U$ and $W$, parallel edges counted separately; the cut **induces** the separation $(\bigcup_{h\in U}V_h,\bigcup_{h\in W}V_h)$. The **petal-separation** at a node $t$ is the separation induced by $(\{t\},V(H)\setminus\{t\})$. A **cycle** of $H$ consists of $m\ge2$ distinct nodes and $m$ distinct edges joining them cyclically (for $m=2$, two parallel edges). $H$ is a **strong cactus** if it is connected and distinct cycles are vertex-disjoint; a **cactus-decomposition** is a graph-decomposition over a strong cactus.
--
--   A separation is **displayed** if it is induced by a cut whose edge set $F$ satisfies (i) $|F|\le1$; (ii) $|F|=2$ and both edges of $F$ lie on a common cycle; or (iii) $|F|\ge2$ and all edges of $F$ are incident with a common P-node. The decomposition is **clique-faithful** if every clique of $G$ (including $\emptyset$ and singletons) lies in the bag of a node that is not a P-node. For a graph isomorphism $\psi:G\to G'$, decompositions of $G$ and $G'$ are **$\psi$-isomorphic** if there is an isomorphism $\varphi$ of their multigraphs (a bijection of nodes with a compatible bijection of edges) with $\psi(V_h)=V'_{\varphi(h)}$ for all nodes $h$; $\psi(S)$ denotes the image of a set of separations.
-- source:
--   Bourneuf, Carmesin, Kurkofka and Planken, An approximate cactus-decomposition for vertex-connectivity, arXiv:2611.01772 (held PDF sha256 78b7d09a…), pp. 1, 22–23, 28, 46, 107 (PDF 4, 25–26, 31, 49, 110), §3.3, Definitions 3.10, 6.5

import Definitions.Def_ApproxCactus_Main_Separations

namespace ApproxCactus.Main

/-- The simple graph underlying a loopless multigraph with node type `N`, edge type `E` and
endpoint map `ends`: two distinct nodes are adjacent iff some edge joins them. -/
def multiSkeleton {N E : Type} (ends : E → Sym2 N) : SimpleGraph N :=
  SimpleGraph.fromRel (fun a b => ∃ e, ends e = s(a, b))

/-- A **graph-decomposition** `(H, V)` of the finite simple graph `G` (§3.3, p. 22) whose
decomposition graph `H` is a finite **loopless multigraph** (parallel edges allowed, so that the
2-cycle `Z₂` of two nodes joined by two parallel edges exists), together with a designated set
`pnode` of **P-nodes** (§3.3; empty for tree-, cycle- and graphic-daisy decompositions).

* `N`, `E`: the nodes and edges of `H`; `ends e` is the unordered pair of endpoints of `e`.
* `bag h = V_h ⊆ V(G)`.
* (H1) `G = ⋃_h G[V_h]`: every vertex lies in a bag, and every edge has both ends in a common bag.
* (H2) for every vertex `v`, the subgraph of `H` induced by `{h : v ∈ V_h}` is connected (in
  particular nonempty). -/
structure Decomp {V : Type*} (G : SimpleGraph V) where
  /-- the nodes of the decomposition graph `H` -/
  N : Type
  /-- the edges of the decomposition graph `H` -/
  E : Type
  [fintypeN : Fintype N]
  [decEqN : DecidableEq N]
  [fintypeE : Fintype E]
  [decEqE : DecidableEq E]
  /-- the two endpoints of each edge of `H` -/
  ends : E → Sym2 N
  /-- `H` has no loops -/
  loopless : ∀ e, ¬ (ends e).IsDiag
  /-- the bags `V_h` -/
  bag : N → Finset V
  /-- the designated P-nodes -/
  pnode : Set N
  /-- (H1), vertices: every vertex of `G` lies in some bag -/
  h1_vertex : ∀ v : V, ∃ h : N, v ∈ bag h
  /-- (H1), edges: every edge of `G` has both ends in some bag -/
  h1_edge : ∀ u v : V, G.Adj u v → ∃ h : N, u ∈ bag h ∧ v ∈ bag h
  /-- (H2): the nodes whose bags contain `v` induce a connected subgraph of `H` -/
  h2 : ∀ v : V, ((multiSkeleton ends).induce {h : N | v ∈ bag h}).Connected

attribute [instance] Decomp.fintypeN Decomp.decEqN Decomp.fintypeE Decomp.decEqE

variable {V : Type*} {G : SimpleGraph V}

/-- The simple graph underlying the decomposition multigraph `H`. -/
def Decomp.skeleton (D : Decomp G) : SimpleGraph D.N := multiSkeleton D.ends

/-- The **adhesion-set** `V_e = V_h ∩ V_{h'}` at the edge `e = hh'` of `H`. -/
def Decomp.adhesion [DecidableEq V] (D : Decomp G) (e : D.E) : Finset V :=
  Sym2.lift ⟨fun a b => D.bag a ∩ D.bag b, fun _ _ => Finset.inter_comm _ _⟩ (D.ends e)

open Classical in
/-- `E_H(U, W)`: the edges of `H` between `U` and its complement `W = V(H) ∖ U`, for the cut
`(U, W)` of `H` (either part may be empty). Parallel edges are counted separately. -/
noncomputable def Decomp.cutEdges (D : Decomp G) (U : Finset D.N) : Finset D.E :=
  Finset.univ.filter (fun e => ∃ a b, D.ends e = s(a, b) ∧ a ∈ U ∧ b ∉ U)

/-- The separation **induced** by the cut `(U, V(H) ∖ U)` of `H`:
`(⋃_{h ∈ U} V_h, ⋃_{h ∉ U} V_h)`. -/
def Decomp.inducedSep [DecidableEq V] (D : Decomp G) (U : Finset D.N) : Finset V × Finset V :=
  (U.biUnion D.bag, Uᶜ.biUnion D.bag)

/-- `C` is the edge set of a **cycle** of the multigraph `H`: there are `m ≥ 2` distinct nodes
`v₀, …, v_{m−1}` and `m` distinct edges `e₀, …, e_{m−1}` with `e_i` joining `v_i` and
`v_{i+1 mod m}`, and `C = {e₀, …, e_{m−1}}`. For `m = 2` this is a pair of parallel edges (`Z₂`). -/
def Decomp.IsCycle (D : Decomp G) (C : Finset D.E) : Prop :=
  ∃ m : ℕ, 2 ≤ m ∧ ∃ (v : Fin m → D.N) (e : Fin m → D.E),
    Function.Injective v ∧ Function.Injective e ∧
    (∀ i, D.ends (e i) = s(v i, v (finRotate m i))) ∧ C = Finset.univ.image e

/-- The nodes of `H` incident with an edge of `C`. -/
def Decomp.edgeNodes (D : Decomp G) (C : Finset D.E) : Set D.N :=
  {n | ∃ e ∈ C, n ∈ D.ends e}

/-- `H` is a **strong cactus** (p. 1, footnote 1): connected, and any two distinct cycles are
vertex-disjoint (so in particular any two cycles share at most one vertex). -/
def Decomp.IsStrongCactus (D : Decomp G) : Prop :=
  D.skeleton.Connected ∧
    ∀ C₁ C₂ : Finset D.E, D.IsCycle C₁ → D.IsCycle C₂ → C₁ ≠ C₂ →
      Disjoint (D.edgeNodes C₁) (D.edgeNodes C₂)

/-- A separation `s` is **displayed** by the decomposition (pp. 22–23): it is induced by a cut
`(U, W)` of `H` whose edge set `F = E_H(U, W)` satisfies
(i) `|F| ≤ 1`; or (ii) `|F| = 2` and both edges of `F` lie on a common cycle of `H`; or
(iii) `|F| ≥ 2` and all edges of `F` are incident with a common P-node.
A **cactus-decomposition** is a `Decomp` whose `H` is a strong cactus (`IsStrongCactus`). -/
def Decomp.IsDisplayed [DecidableEq V] (D : Decomp G) (s : Finset V × Finset V) : Prop :=
  ∃ U : Finset D.N, D.inducedSep U = s ∧
    ((D.cutEdges U).card ≤ 1 ∨
      ((D.cutEdges U).card = 2 ∧ ∃ C, D.IsCycle C ∧ D.cutEdges U ⊆ C) ∨
      (2 ≤ (D.cutEdges U).card ∧ ∃ p ∈ D.pnode, ∀ e ∈ D.cutEdges U, p ∈ D.ends e))

/-- A cactus-decomposition is **clique-faithful** (p. 107) if every clique of `G` (a set of
pairwise adjacent vertices; `∅` and singletons included) is contained in the bag of a node that is
not a P-node. -/
def Decomp.IsCliqueFaithful (D : Decomp G) : Prop :=
  ∀ K : Finset V, G.IsClique (K : Set V) → ∃ h : D.N, h ∉ D.pnode ∧ K ⊆ D.bag h

/-- The **centre** of the decomposition (Definition 3.10, p. 28): the intersection of all bags. -/
def Decomp.centre [Fintype V] [DecidableEq V] (D : Decomp G) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => ∀ h : D.N, v ∈ D.bag h)

/-- The **petal-separation** at the node `t` (p. 23): the separation induced by
`({t}, V(H) ∖ {t})`. -/
def Decomp.petalSep [DecidableEq V] (D : Decomp G) (t : D.N) : Finset V × Finset V :=
  D.inducedSep {t}

/-- **`ψ`-isomorphic** decompositions (Definition 6.5, p. 46): for an isomorphism `ψ : G ≅ G'`,
there is an isomorphism `φ` of the decomposition multigraphs (a bijection of nodes together with a
compatible bijection of edges) such that `ψ(V_h) = V'_{φ(h)}` for every node `h`. -/
def PsiIso {V W : Type*} [DecidableEq W] {G : SimpleGraph V} {G' : SimpleGraph W}
    (ψ : G ≃g G') (D : Decomp G) (D' : Decomp G') : Prop :=
  ∃ (φ : D.N ≃ D'.N) (χ : D.E ≃ D'.E),
    (∀ e, D'.ends (χ e) = Sym2.map φ (D.ends e)) ∧
    ∀ h, (D.bag h).map ψ.toEquiv.toEmbedding = D'.bag (φ h)

/-- The image `ψ(S)` of a set of separations under a graph isomorphism `ψ`. -/
def mapSepSet {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W} (ψ : G ≃g G')
    (S : Set (Finset V × Finset V)) : Set (Finset W × Finset W) :=
  (fun s => (s.1.map ψ.toEquiv.toEmbedding, s.2.map ψ.toEquiv.toEmbedding)) '' S

end ApproxCactus.Main



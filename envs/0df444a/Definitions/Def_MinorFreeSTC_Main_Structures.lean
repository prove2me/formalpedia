-- Prove2me | Definitions.Def_MinorFreeSTC_Main_Structures
-- name    : MinorFreeSTC_Main_Structures
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:17:23.380283+00:00
-- url     : https://prove2.me/theorems/01f7160b-3d6d-48b1-ae28-6f04dc6c780b
-- title:
--   Weak 2-reachability (Def. 8), quotients and shortcut partitions (Def. 9), the conflict graph (§5), tilings and buffered cop decompositions (Defs. 10–12)
-- statement:
--   **Weak 2-reachability (Definition 8).** For a total order $\pi$ on $V$ (an injective rank $V\to\mathbb N$), $u$ is weakly 2-reachable from $v$ if some $v$–$u$ path with at most two edges has $u$ as its $\pi$-minimum; $\mathrm{WReach}^\pi_2(v)$ is the set of such $u$ (it contains $v$).
--
--   **Quotient and shortcut partitions (Definition 9).** For a partition $\mathcal C$, $G/\mathcal C$ has one vertex per cluster and an edge between distinct clusters joined by an edge of $G$ (unit weights). $\mathcal C$ is an **$(\epsilon,h)$-shortcut partition** if every cluster has strong diameter at most $\epsilon\operatorname{diam}(G)$ and, for all $u,v$ and every shortest $u$–$v$ path $Q$ of $G$, there is a path in $G/\mathcal C$ from the cluster of $u$ to the cluster of $v$ with at most
--   $$\epsilon h\left\lceil\frac{d_G(u,v)}{\epsilon\operatorname{diam}(G)}\right\rceil$$
--   hops, using only clusters that meet $Q$.
--
--   **Conflict graph (§5).** For a $\Delta$-diameter strong $(\alpha,\tau)$-sparse partition $\mathcal P$, put $Z_P=B_G(P,\Delta/(2\alpha))$; the conflict graph $X$ has vertex set $\mathcal P$ and joins distinct $P,Q$ when $Z_P\cap Z_Q\ne\emptyset$. $|E(X[S])|$ counts its edges inside $S\subseteq\mathcal P$.
--
--   **Tilings and buffered cop decompositions (Definitions 10–12).** A $\delta$-tiling is a partition into tiles of strong diameter at most $\delta$. A **$\Delta$-radius $\beta$-buffered $\omega$-width cop decomposition** is a partition $\mathcal S$ of $V$ into connected supernodes, a rooted tree $\mathcal T$ on $\mathcal S$ and, for each supernode $\eta$, a rooted skeleton tree $T_\eta\subseteq G[\eta]$ with root $c_\eta$; $\mathrm{dom}(\eta)$ is the subgraph induced by the union of the supernodes in the subtree of $\eta$. It satisfies: *Supernode Radius* $d_{G[\eta]}(v,V(T_\eta))\le\Delta$ for $v\in\eta$; *Shortest-Path Skeletons* $T_\eta$ has at most $\omega$ leaves besides its root and $d_{T_\eta}(c_\eta,x)=d_{\mathrm{dom}(\eta)}(c_\eta,x)$; *Skeleton–Ancestor Adjacency* an edge between $\mathrm{dom}(\eta)$ and a proper ancestor $X$ implies one between $V(T_\eta)$ and $X$; *Supernode Buffer* for a proper ancestor $X$ with no edge to $\eta$, $d_{\mathrm{dom}(X)}(v,X)>\beta$ for all $v\in\mathrm{dom}(\eta)$; *Width* the bags $B_\eta=\eta\cup\bigcup\{X$ proper ancestor adjacent to $\eta\}$ form a tree decomposition along $\mathcal T$, each the union of at most $\omega$ supernodes. It is **$\mathcal P$-tiled** if every tile lies in one supernode.
--
--   **Formalization Note.** A cop decomposition is stored as `CopData`: supernodes, parent pointers (`none` at the root), roots, skeleton vertex sets and skeleton edges (a subgraph of $G$). "Rooted tree" is: parents lie in $\mathcal S$, exactly one supernode has no parent, and no supernode is its own proper ancestor. The tree-decomposition clause is: every edge of $G$ lies in a bag, and the supernodes whose bag contains $v$ induce a connected subgraph of $\mathcal T$.
-- source:
--   Filtser, Fletcher, Hershkowitz, Milenković, (1 + ϵ)-Distortion Spanning Tree Covers of Minor-Free Graphs with Size O(log log n), STOC 2027 submission (manuscript sha256 f475e254…), p. 16 (Definition 8), p. 17 (quotient), p. 18 (Definition 9), p. 19 (conflict graph), pp. 21–22 (Definitions 10–12)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_MinorFreeSTC_Main_Graphs

set_option autoImplicit false

open scoped ENNReal

namespace MinorFreeSTC.Main

open ARTreeCover

/-!
# Weak 2-reachability, shortcut partitions, the conflict graph, buffered cop decompositions

Filtser, Fletcher, Hershkowitz, Milenković, *(1 + ϵ)-Distortion Spanning Tree Covers of Minor-Free
Graphs with Size O(log log n)*, STOC 2027 submission (manuscript sha256 f475e254…): Definition 8
(p. 16, PDF 18), the quotient `G/P` (p. 17, PDF 19), Definition 9 (p. 18, PDF 20), the conflict
graph of §5 (p. 19, PDF 21), Definitions 10–12 (pp. 21–22, PDF 23–24).

* A total order `π` on `V` is an injective rank `π : V → ℕ` (`u` precedes `v` iff `π u < π v`).
* A cop decomposition stores its supernodes `S`, the parent of each supernode in the rooted tree
  `T` (`none` at the root), the root `c_η` and vertex set of each skeleton, and the skeleton's
  edges as a subgraph of `G`.
-/

variable {V : Type}

/-! ### Weak 2-reachability (Definition 8) -/

/-- Definition 8: `WReach^π_2(v)`, the vertices `u` weakly 2-reachable from `v`: there is a
`v`–`u` path with at most two edges on which `u` is the `π`-minimum vertex. -/
def WReach2 (G : SimpleGraph V) (π : V → ℕ) (v : V) : Set V :=
  {u | ∃ p : G.Walk v u, p.IsPath ∧ p.length ≤ 2 ∧ ∀ x ∈ p.support, π u ≤ π x}

/-! ### Quotients and shortcut partitions (Definition 9) -/

/-- The quotient `G/𝒞` (p. 17) on the clusters of `𝒞`: distinct clusters are adjacent when some
edge of `G` joins them (no loops, no parallel edges; unit weights, so hops are walk lengths). -/
def quotient (G : WGraph V) (𝒞 : Finset (Finset V)) : SimpleGraph {C // C ∈ 𝒞} :=
  SimpleGraph.fromRel fun A B => ∃ a ∈ A.1, ∃ b ∈ B.1, G.graph.Adj a b

/-- Definition 9 (p. 18): `𝒞` is an `(ϵ, h)`-shortcut partition of `G`: a partition into clusters
of strong diameter at most `ϵ · diam(G)` such that, for all `u, v` and every shortest `u`–`v`
path `Q` of `G`, there is a path in `G/𝒞` from the cluster of `u` to the cluster of `v` with at
most `ϵh⌈d_G(u, v)/(ϵ · diam(G))⌉` hops, all of whose clusters meet `Q`. -/
def IsShortcutPartition (G : WGraph V) (𝒞 : Finset (Finset V)) (ϵ h : ℝ) : Prop :=
  IsPartition 𝒞 ∧ DiamLe G 𝒞 (ϵ * (diamG G).toReal) ∧
    ∀ (u v : V) (Q : G.graph.Walk u v), IsShortestPath G Q →
      ∀ (Cu Cv : {C // C ∈ 𝒞}), u ∈ Cu.1 → v ∈ Cv.1 →
        ∃ p : (quotient G 𝒞).Walk Cu Cv,
          (p.length : ℝ) ≤ ϵ * h * ⌈(G.dist u v).toReal / (ϵ * (diamG G).toReal)⌉ ∧
            ∀ X ∈ p.support, ∃ x ∈ Q.support, x ∈ X.1

/-! ### The conflict graph (§5) -/

/-- The conflict graph `X` of a `∆`-diameter strong `(α, τ)`-sparse partition `P` (p. 19): vertex
set `P`; distinct `P, Q ∈ P` adjacent iff `Z_P ∩ Z_Q ≠ ∅`, where `Z_P = B_G(P, ∆/(2α))`. -/
def conflictGraph (G : WGraph V) (P : Finset (Finset V)) (Δ α : ℝ) : SimpleGraph (Finset V) :=
  SimpleGraph.fromRel fun A B => A ∈ P ∧ B ∈ P ∧
    ∃ x, x ∈ ballSet G (A : Set V) (Δ / (2 * α)) ∧ x ∈ ballSet G (B : Set V) (Δ / (2 * α))

open Classical in
/-- `|E(X[S])|`, the number of edges of the subgraph of `X` induced by `S` (each unordered pair
counted once). -/
noncomputable def inducedEdgeCount {α : Type} (X : SimpleGraph α) (S : Finset α) : ℕ :=
  ((S ×ˢ S).filter fun p => X.Adj p.1 p.2).card / 2

/-! ### Tilings and buffered cop decompositions (Definitions 10–12) -/

/-- Definition 10 (p. 21): `P` is a `δ`-tiling: a partition into tiles of strong diameter `≤ δ`. -/
def IsTiling (G : WGraph V) (P : Finset (Finset V)) (δ : ℝ) : Prop :=
  IsPartition P ∧ DiamLe G P δ

/-- The data of a cop decomposition of `G` (Definition 11): supernodes, the rooted tree `T` on
them, and the rooted skeleton `T_η ⊆ G[η]` of each supernode. -/
structure CopData (G : WGraph V) where
  /-- The supernodes. -/
  S : Finset (Finset V)
  /-- The parent of a supernode in `T` (`none` at the root). -/
  parent : Finset V → Option (Finset V)
  /-- The root `c_η` of the skeleton of `η`. -/
  root : Finset V → V
  /-- The vertex set `V(T_η)` of the skeleton of `η`. -/
  skelV : Finset V → Finset V
  /-- The edges of the skeleton of `η`. -/
  skel : Finset V → SimpleGraph V
  /-- Skeleton edges are edges of `G`. -/
  skel_le : ∀ η, skel η ≤ G.graph

namespace CopData

variable {G : WGraph V}

/-- The skeleton `T_η` as a weighted graph with the weights of `G`. -/
def skelGraph (D : CopData G) (η : Finset V) : WGraph V where
  graph := D.skel η
  w := G.w
  w_pos := fun e he => G.w_pos e (SimpleGraph.edgeSet_mono (D.skel_le η) he)

/-- `X` is a proper ancestor of `η` in `T`. -/
def IsProperAncestor (D : CopData G) (X η : Finset V) : Prop :=
  Relation.TransGen (fun A B => D.parent B = some A) X η

/-- The vertex set of `dom(η)`: the union of the supernodes of the subtree of `T` rooted at `η`. -/
def domSet (D : CopData G) (η : Finset V) : Set V :=
  {v | ∃ X ∈ D.S, (X = η ∨ D.IsProperAncestor η X) ∧ v ∈ X}

/-- Some edge of `G` joins `A` and `B`. -/
def EdgeBetween (G : WGraph V) (A B : Set V) : Prop := ∃ a ∈ A, ∃ b ∈ B, G.graph.Adj a b

/-- The bag `B_η = η ∪ ⋃{X ∈ S : X a proper ancestor of η with an edge between X and η}`. -/
def bag (D : CopData G) (η : Finset V) : Set V :=
  (η : Set V) ∪ {v | ∃ X ∈ D.S, D.IsProperAncestor X η ∧ EdgeBetween G X η ∧ v ∈ X}

/-- The tree `T` as a simple graph on supernodes (child–parent adjacency). -/
def treeGraph (D : CopData G) : SimpleGraph (Finset V) :=
  SimpleGraph.fromRel fun A B => D.parent A = some B

open Classical in
/-- The leaves of `T_η` other than its root. -/
noncomputable def leavesExRoot (D : CopData G) (η : Finset V) : Finset V :=
  (D.skelV η).filter fun x => x ≠ D.root η ∧ ((D.skel η).neighborSet x).ncard ≤ 1

end CopData

open CopData in
open Classical in
/-- Definition 11 (p. 21): `D` is a `∆`-radius `β`-buffered `ω`-width cop decomposition of `G`:
a partition `S` into connected supernodes, a rooted tree `T` on `S`, rooted skeleton trees
`T_η ⊆ G[η]`, with the properties Supernode Radius, Shortest-Path Skeletons, Skeleton–Ancestor
Adjacency, Supernode Buffer and Width. -/
def IsCopDecomposition [Fintype V] (G : WGraph V) (D : CopData G) (Δ β : ℝ) (ω : ℕ) : Prop :=
  -- partition into connected supernodes
  (IsPartition D.S ∧ ∀ η ∈ D.S, (G.graph.induce (η : Set V)).Connected) ∧
  -- `T` is a rooted tree on `S`
  ((∀ η ∈ D.S, ∀ X, D.parent η = some X → X ∈ D.S) ∧ (∃! ρ, ρ ∈ D.S ∧ D.parent ρ = none) ∧
    ∀ η ∈ D.S, ¬ D.IsProperAncestor η η) ∧
  -- each skeleton is a tree in `G[η]` rooted at `c_η`
  (∀ η ∈ D.S, D.skelV η ⊆ η ∧ D.root η ∈ D.skelV η ∧
    (∀ x y, (D.skel η).Adj x y → x ∈ D.skelV η ∧ y ∈ D.skelV η) ∧
    ((D.skel η).induce (D.skelV η : Set V)).IsTree) ∧
  -- Supernode Radius
  (∀ η ∈ D.S, ∀ v ∈ η,
    distInToSet G (η : Set V) v (D.skelV η : Set V) ≤ ENNReal.ofReal Δ) ∧
  -- Shortest-Path Skeletons
  (∀ η ∈ D.S, (D.leavesExRoot η).card ≤ ω ∧
    ∀ x ∈ D.skelV η, (D.skelGraph η).dist (D.root η) x = G.distIn (D.domSet η) (D.root η) x) ∧
  -- Skeleton–Ancestor Adjacency
  (∀ η ∈ D.S, ∀ X ∈ D.S, D.IsProperAncestor X η →
    EdgeBetween G (D.domSet η) (X : Set V) → EdgeBetween G (D.skelV η : Set V) (X : Set V)) ∧
  -- Supernode Buffer
  (∀ η ∈ D.S, ∀ X ∈ D.S, D.IsProperAncestor X η → ¬ EdgeBetween G (η : Set V) (X : Set V) →
    ∀ v ∈ D.domSet η, ENNReal.ofReal β < distInToSet G (D.domSet X) v (X : Set V)) ∧
  -- Width: the bags form a tree decomposition along `T`, each a union of at most `ω` supernodes
  ((∀ u v, G.graph.Adj u v → ∃ η ∈ D.S, u ∈ D.bag η ∧ v ∈ D.bag η) ∧
    (∀ v : V, (D.treeGraph.induce {η | η ∈ D.S ∧ v ∈ D.bag η}).Connected) ∧
    ∀ η ∈ D.S,
      1 + (D.S.filter fun X => D.IsProperAncestor X η ∧ EdgeBetween G (X : Set V) η).card ≤ ω)

/-- Definition 12 (p. 22), Tiling: every tile of `P` lies in a single supernode. -/
def IsTiledBy {G : WGraph V} (D : CopData G) (P : Finset (Finset V)) : Prop :=
  ∀ T ∈ P, ∃ η ∈ D.S, T ⊆ η

end MinorFreeSTC.Main



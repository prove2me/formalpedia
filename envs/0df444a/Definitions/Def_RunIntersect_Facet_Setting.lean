-- Prove2me | Definitions.Def_RunIntersect_Facet_Setting
-- name    : RunIntersect_Facet_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T15:34:42.541361+00:00
-- url     : https://prove2.me/theorems/2d286f03-c95c-4233-aaec-3adc1639a333
-- title:
--   §2–§2.4, pp. 1008–1017 — hypergraphs, S_G and MP_G (1), MP^LP_G (8), running intersection orderings (2)–(3), leaves, inequalities (5), MP^RI_G, facets, support hypergraphs
-- statement:
--   This file fixes the objects of Sections 1–2 of Del Pia and Khajavirad, *The running intersection relaxation of the multilinear polytope*.
--
--   **Hypergraphs.** A hypergraph $G=(V,E)$ consists of a finite node set $V$ and a set $E$ of subsets of $V$, each of cardinality at least two (no loops, no parallel edges, as the paper assumes throughout).
--
--   **Multilinear set and polytope.** The multilinear set of $G$ is
--   $$\mathcal S_G=\Big\{z\in\{0,1\}^{V+E}:\ z_e=\prod_{v\in e}z_v\ \ \forall e\in E\Big\},$$
--   and the multilinear polytope is $\mathrm{MP}_G=\operatorname{conv}\mathcal S_G$. The standard linearization is
--   $$\mathrm{MP}^{\mathrm{LP}}_G=\Big\{z:\ z_v\le 1\ \forall v\in V;\ z_e\ge 0,\ z_e\ge \sum_{v\in e}z_v-|e|+1\ \forall e\in E;\ z_e\le z_v\ \forall e\in E,\ v\in e\Big\}.$$
--
--   **Running intersection property.** A multiset $F$ of sets has the running intersection property if its elements can be ordered $p_1,\dots,p_m$ so that for each $k=2,\dots,m$ there is $j<k$ with $p_k\cap\big(\bigcup_{i<k}p_i\big)\subseteq p_j$; such an ordering is a running intersection ordering. It induces the sets $N(p_1)=\emptyset$ and $N(p_k)=p_k\cap\bigcup_{i<k}p_i$. An element of $F$ is a *leaf* if it is the last element of some running intersection ordering.
--
--   **Running intersection inequalities.** Let $e_0\in E$ and let $e_k$, $k\in K$, be edges other than $e_0$ adjacent to $e_0$ such that the multiset $\tilde E=\{e_0\cap e_k:k\in K\}$ has the running intersection property. Fix a running intersection ordering of $\tilde E$ with sets $N(e_0\cap e_k)$, and for each $k$ with $N(e_0\cap e_k)\ne\emptyset$ a node $u_k\in N(e_0\cap e_k)$. The running intersection inequality is
--   $$-\sum_{k\in K:\,N(e_0\cap e_k)\neq\emptyset} z_{u_k}+\sum_{v\in e_0\setminus\bigcup_{k\in K}e_k} z_v+\sum_{k\in K}z_{e_k}-z_{e_0}\ \le\ \omega-1,$$
--   where $\omega$ is the number of connected components of the hypergraph $\tilde G=(e_0,\tilde E)$ (which may have loops and parallel edges). The running intersection relaxation $\mathrm{MP}^{\mathrm{RI}}_G$ is $\mathrm{MP}^{\mathrm{LP}}_G$ intersected with all running intersection inequalities.
--
--   **Facets and support hypergraphs.** An inequality $\ell(z)\le b$ defines a facet of a set $P$ if it is valid on $P$ and the face $P\cap\{\ell=b\}$ is nonempty and has affine dimension $\dim P-1$. The support hypergraph of a running intersection inequality centered at $e_0$ with neighbors $e_k$, $k\in K$, is the hypergraph with node set $e_0\cup\bigcup_{k\in K}e_k$ and edge set $\{e_0\}\cup\{e_k:k\in K\}$.
--
--   These are the objects in which Proposition 4 and its supporting results are stated.
--
--   **Formalization Note** Nodes are elements of a finite type `α`; the space $\mathbb R^{V+E}$ of every hypergraph is embedded in the single space `α ⊕ Finset α → ℝ`, with coordinates outside $V+E$ pinned to $0$ inside the definitions of $\mathcal S_G$ and $\mathrm{MP}^{\mathrm{LP}}_G$. Orderings are lists indexed from $0$ (the paper's $k=2,\dots,m$ is `0 < k`). The number of connected components is that of the 2-section graph on the node set (an isolated node is its own component, a loop connects nothing). The data of an inequality (`RIData`) carries the center, the neighbor set $K\subseteq E\setminus\{e_0\}$ (distinct edges), a duplicate-free ordering of $K$ whose traces form a running intersection ordering of $\tilde E$, and the choice $k\mapsto u_k$; the first sum of (5) runs over neighbors $k$, so a node chosen for several $k$ gets coefficient $-2$, $-3$, … as in Example 1. Dimensions are compared as $\dim F+1=\dim P$ with $F$ nonempty, so no truncated subtraction occurs. The support hypergraph `suppHg` takes the structural facts $|e_0|\ge 2$, $|e_k|\ge 2$ as arguments; that its node and edge sets are those of $G(a)$ for the coefficient vector $a$ of (5) follows because $a_{e_0}=-1$, $a_{e_k}=1$ and every node with $a_v\neq 0$ lies in $e_0$.
-- source:
--   Del Pia and Khajavirad, The running intersection relaxation of the multilinear polytope, Math. Oper. Res. 46 (2021), pp. 1008, 1010–1016, (1)–(5), (8), definitions of support hypergraph (p. 1010), leaf (pp. 1010–1011), MP^RI (p. 1014)

import Mathlib

namespace RunIntersect.Facet

/-- A hypergraph `G = (V, E)` without loops or parallel edges (Del Pia and Khajavirad, §2, p. 1010):
`E` is a set of subsets of `V`, each of cardinality at least two. -/
structure Hypergraph (α : Type*) [DecidableEq α] where
  V : Finset α
  E : Finset (Finset α)
  edge_subset : ∀ e ∈ E, e ⊆ V
  two_le_card : ∀ e ∈ E, 2 ≤ e.card

variable {α : Type*} [DecidableEq α]

/-- The coordinates of `ℝ^{V+E}` inside the fixed space `α ⊕ Finset α → ℝ`:
`inl v` for `v ∈ V` (the variable `z_v`) and `inr e` for `e ∈ E` (the variable `z_e`). -/
def Hypergraph.coords (H : Hypergraph α) : Set (α ⊕ Finset α) :=
  {p | (∃ v ∈ H.V, p = Sum.inl v) ∨ (∃ e ∈ H.E, p = Sum.inr e)}

/-- The multilinear set `S_G` of (1), p. 1008: `z ∈ {0,1}^{V+E}` with `z_e = ∏_{v ∈ e} z_v`
for every edge; coordinates outside `V + E` are pinned to `0`. -/
def multilinearSet (H : Hypergraph α) : Set (α ⊕ Finset α → ℝ) :=
  {z | (∀ v ∈ H.V, z (Sum.inl v) = 0 ∨ z (Sum.inl v) = 1) ∧
       (∀ e ∈ H.E, z (Sum.inr e) = ∏ v ∈ e, z (Sum.inl v)) ∧
       ∀ p ∉ H.coords, z p = 0}

/-- The multilinear polytope `MP_G = conv S_G`, p. 1008. -/
def MP (H : Hypergraph α) : Set (α ⊕ Finset α → ℝ) :=
  convexHull ℝ (multilinearSet H)

/-- The standard linearization `MP^LP_G` of (8), p. 1014 (exactly the printed system). -/
def MPLP (H : Hypergraph α) : Set (α ⊕ Finset α → ℝ) :=
  {z | (∀ v ∈ H.V, z (Sum.inl v) ≤ 1) ∧
       (∀ e ∈ H.E, 0 ≤ z (Sum.inr e) ∧
          (∑ v ∈ e, z (Sum.inl v)) - (e.card : ℝ) + 1 ≤ z (Sum.inr e) ∧
          ∀ v ∈ e, z (Sum.inr e) ≤ z (Sum.inl v)) ∧
       ∀ p ∉ H.coords, z p = 0}

/-- `⋃_{i<k} p_i` for the list `l = p_0, p_1, …` (0-indexed). -/
def prefixUnion (l : List (Finset α)) (k : ℕ) : Finset α :=
  ((List.range k).filterMap (fun i => l[i]?)).foldr (· ∪ ·) ∅

/-- A running intersection ordering, (2), p. 1010 (0-indexed: the paper's `k = 2, …, m` is
`0 < k`): for each `k > 0` there is `j < k` with `p_k ∩ (⋃_{i<k} p_i) ⊆ p_j`. -/
def IsRIOrder (l : List (Finset α)) : Prop :=
  ∀ k (hk : k < l.length), 0 < k → ∃ j, ∃ hj : j < k, l[k] ∩ prefixUnion l k ⊆ l[j]'(by omega)

/-- The sets `N(p_k)` of (3), p. 1010: `N(p_0) = ∅` and `N(p_k) = p_k ∩ ⋃_{i<k} p_i`
(and `∅` for an index past the end of the list). -/
def Nset (l : List (Finset α)) (k : ℕ) : Finset α :=
  (l[k]?.getD ∅) ∩ prefixUnion l k

/-- A multiset of sets has the running intersection property, p. 1010. -/
def HasRIP (F : Multiset (Finset α)) : Prop :=
  ∃ l : List (Finset α), (l : Multiset (Finset α)) = F ∧ IsRIOrder l

/-- A leaf of `F`, pp. 1010–1011: the last element of some running intersection ordering of `F`. -/
def IsLeaf (F : Multiset (Finset α)) (f : Finset α) : Prop :=
  ∃ l : List (Finset α), (l : Multiset (Finset α)) = F ∧ IsRIOrder l ∧ l.getLast? = some f

/-- The 2-section graph on the node set `W` of the multiset of edges `F` (loops and parallel
edges allowed): two distinct nodes are adjacent iff some edge contains both. -/
def twoSection (W : Finset α) (F : Multiset (Finset α)) : SimpleGraph W where
  Adj u v := u ≠ v ∧ ∃ f ∈ F, (u : α) ∈ f ∧ (v : α) ∈ f
  symm := by
    constructor
    intro u v h
    obtain ⟨h, f, hf, hu, hv⟩ := h
    exact ⟨Ne.symm h, f, hf, hv, hu⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The number of connected components of the hypergraph `(W, F)` (p. 1011), computed as the
number of connected components of its 2-section graph; an isolated node is its own component. -/
noncomputable def numComponents (W : Finset α) (F : Multiset (Finset α)) : ℕ :=
  Nat.card (twoSection W F).ConnectedComponent

/-- The set `N(e₀ ∩ e_k)` of (3) attached to the neighbor `k`, for the running intersection
ordering `ord` of the neighbors (the traces `e₀ ∩ e_k` are ordered as `ord`). -/
def traceN (e0 : Finset α) (ord : List (Finset α)) (k : Finset α) : Finset α :=
  Nset (ord.map (e0 ∩ ·)) (ord.idxOf k)

/-- The data of a running intersection inequality (4)–(5), p. 1011, for the hypergraph `H`:
a center `e0 ∈ E`, a set `K` of neighbors (edges other than `e0` adjacent to `e0`), an ordering
`ord` of `K` whose traces `e₀ ∩ e_k` form a running intersection ordering of `Ẽ`, and a choice
`u k ∈ N(e₀ ∩ e_k)` for every neighbor with `N(e₀ ∩ e_k) ≠ ∅`. -/
structure RIData (H : Hypergraph α) where
  e0 : Finset α
  K : Finset (Finset α)
  ord : List (Finset α)
  u : Finset α → α
  e0_mem : e0 ∈ H.E
  K_sub : K ⊆ H.E.erase e0
  adj : ∀ k ∈ K, (e0 ∩ k).Nonempty
  ord_nodup : ord.Nodup
  ord_toFinset : ord.toFinset = K
  ord_RI : IsRIOrder (ord.map (e0 ∩ ·))
  u_mem : ∀ k ∈ K, (traceN e0 ord k).Nonempty → u k ∈ traceN e0 ord k

variable {H : Hypergraph α}

/-- `N(e₀ ∩ e_k)` for the data `d`. -/
def RIData.N (d : RIData H) (k : Finset α) : Finset α :=
  traceN d.e0 d.ord k

/-- Left-hand side of the running intersection inequality (5):
`− ∑_{k ∈ K : N(e₀∩e_k) ≠ ∅} z_{u_k} + ∑_{v ∈ e₀ ∖ ⋃_k e_k} z_v + ∑_{k ∈ K} z_{e_k} − z_{e₀}`.
The first sum runs over neighbors `k`, so a node chosen as `u_k` for several `k` is counted
with multiplicity. -/
def RIData.lhs (d : RIData H) (z : α ⊕ Finset α → ℝ) : ℝ :=
  -(∑ k ∈ d.K.filter (fun k => (d.N k).Nonempty), z (Sum.inl (d.u k)))
    + (∑ v ∈ d.e0 \ d.K.biUnion id, z (Sum.inl v))
    + (∑ k ∈ d.K, z (Sum.inr k)) - z (Sum.inr d.e0)

/-- Right-hand side `ω − 1` of (5), with `ω` the number of connected components of
`G̃ = (e₀, Ẽ)`, `Ẽ = {e₀ ∩ e_k : k ∈ K}` a multiset. -/
noncomputable def RIData.rhs (d : RIData H) : ℝ :=
  (numComponents d.e0 (d.K.val.map (d.e0 ∩ ·)) : ℝ) - 1

/-- The running intersection relaxation `MP^RI_G`, p. 1014: `MP^LP_G` cut by every running
intersection inequality (every center, neighbor set, ordering and choice of the `u_k`). -/
def MPRI (H : Hypergraph α) : Set (α ⊕ Finset α → ℝ) :=
  MPLP H ∩ {z | ∀ d : RIData H, d.lhs z ≤ d.rhs}

/-- The inequality `ℓ z ≤ b` defines a facet of `P`: it is valid on `P`, the face it cuts out
is nonempty, and that face has affine dimension one less than `P`. -/
def DefinesFacet (P : Set (α ⊕ Finset α → ℝ)) (ℓ : (α ⊕ Finset α → ℝ) → ℝ) (b : ℝ) : Prop :=
  (∀ z ∈ P, ℓ z ≤ b) ∧ (P ∩ {z | ℓ z = b}).Nonempty ∧
    Module.finrank ℝ (vectorSpan ℝ (P ∩ {z | ℓ z = b})) + 1 = Module.finrank ℝ (vectorSpan ℝ P)

/-- The support hypergraph of a running intersection inequality centered at `e0` with
neighbors `K` (§2, p. 1010): node set `e₀ ∪ ⋃_{k ∈ K} e_k`, edge set `{e₀} ∪ K`. -/
def suppHg (e0 : Finset α) (K : Finset (Finset α)) (he0 : 2 ≤ e0.card)
    (hK : ∀ k ∈ K, 2 ≤ k.card) : Hypergraph α where
  V := e0 ∪ K.biUnion id
  E := insert e0 K
  edge_subset := by
    intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact Finset.subset_union_left
    · exact (Finset.subset_biUnion_of_mem id he).trans Finset.subset_union_right
  two_le_card := by
    intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact he0
    · exact hK e he

end RunIntersect.Facet



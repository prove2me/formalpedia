-- Prove2me | Definitions.Def_RunIntersect_Tight_Setting
-- name    : RunIntersect_Tight_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T15:34:44.847304+00:00
-- url     : https://prove2.me/theorems/6f838565-4b70-430d-8076-c5b1aa112b25
-- title:
--   §2–§5.3, pp. 1008–1035 — hypergraphs, S_G and MP_G (1), MP^LP_G (8), running intersection inequalities (2)–(5), MP^RI_G, β-cycles, kites, t-laminarity, system (20), G⁺ (21)
-- statement:
--   This file sets up the objects of Del Pia and Khajavirad's study of the running intersection relaxation of the multilinear polytope.
--
--   **Hypergraphs.** A hypergraph $G=(V,E)$ has a finite node set $V$ and a set $E$ of subsets of $V$, each of cardinality at least two (no loops, no parallel edges, as the paper assumes throughout). Two edges are adjacent if they intersect. A node is isolated if it lies in no edge.
--
--   **Multilinear set and polytope (1).** Points live in $\mathbb R^{V+E}$, with one coordinate $z_v$ per node and one coordinate $z_e$ per edge. The multilinear set is
--   $$\mathcal S_G=\Big\{z\in\{0,1\}^{V+E} : z_e=\prod_{v\in e}z_v\ \ \forall e\in E\Big\},$$
--   and the multilinear polytope is $\mathrm{MP}_G=\operatorname{conv}\mathcal S_G$.
--
--   **Standard linearization (8).**
--   $$\mathrm{MP}^{\mathrm{LP}}_G=\Big\{z : z_v\le 1\ \forall v\in V;\ z_e\ge 0,\ z_e\ge \sum_{v\in e}z_v-|e|+1\ \forall e\in E;\ z_e\le z_v\ \forall e\in E,\ v\in e\Big\}.$$
--
--   **Running intersection orderings (2)–(3).** An ordering $p_1,\dots,p_m$ of a multiset $F$ of sets is a running intersection ordering if for each $k\ge 2$ there is $j<k$ with $p_k\cap\bigcup_{i<k}p_i\subseteq p_j$; $F$ has the running intersection property if it has such an ordering. The ordering induces $N(p_1)=\emptyset$ and $N(p_k)=p_k\cap\bigcup_{i<k}p_i$.
--
--   **Running intersection inequalities (4)–(5).** Let $e_0\in E$ (the center) and let $e_k$, $k\in K$, be edges adjacent to $e_0$ (the neighbors) such that $\tilde E=\{e_0\cap e_k:k\in K\}$ has the running intersection property. Fix a running intersection ordering of $\tilde E$, and for each $k$ with $N(e_0\cap e_k)\neq\emptyset$ a node $u_k\in N(e_0\cap e_k)$. The inequality is
--   $$-\sum_{k\in K:\,N(e_0\cap e_k)\neq\emptyset} z_{u_k}+\sum_{v\in e_0\setminus\bigcup_{k\in K}e_k} z_v+\sum_{k\in K}z_{e_k}-z_{e_0}\le \omega-1,$$
--   where $\omega$ is the number of connected components of the hypergraph $\tilde G=(e_0,\tilde E)$ (which may have loops and parallel edges; an isolated node is a component). The running intersection relaxation $\mathrm{MP}^{\mathrm{RI}}_G$ is $\mathrm{MP}^{\mathrm{LP}}_G$ together with all such inequalities.
--
--   **Acyclicity, kites, laminarity.** A β-cycle of length $t\ge 3$ is a sequence of distinct nodes $v_1,\dots,v_t$ and distinct edges $e_1,\dots,e_t$ such that $v_i$ lies in $e_{i-1}$ and $e_i$ (indices mod $t$) and in no other $e_j$; $G$ is β-acyclic if it has none. A kite is three edges $e_0,e_1,e_2$ with $|e_0\cap e_1\cap e_2|\ge 2$, $(e_0\cap e_1)\setminus e_2\neq\emptyset$, $(e_0\cap e_2)\setminus e_1\neq\emptyset$. $G$ is $t$-laminar if any two distinct edges meeting in at least $t$ nodes are strictly nested. The section hypergraph induced by $W$ keeps the edges inside $W$; the subhypergraph $G_W$ has the edges $e\cap W$ with $|e\cap W|\ge 2$.
--
--   **System (20).** An edge is maximal if it is strictly contained in no other edge. For $e\in E$, $I(e)$ is the set of nodes and edges strictly inside $e$ that are strictly contained in no edge $e'\subset e$; $\omega(e)$ is the number of components of $H_e=(e,I(e)\cap E)$ and $\delta_e(v)$ the number of edges of $H_e$ containing $v$. System (20) consists of $z_v\le 1$; $-z_p\le 0$ for every node or edge $p$ strictly contained in no edge; $z_e\le z_p$ for $p\in I(e)$; and
--   $$\sum_{v\in e}(1-\delta_e(v))z_v+\sum_{p\in I(e)\cap E}z_p-z_e\le\omega(e)-1\qquad\forall e\in E.$$
--
--   **Decomposition and lifting.** $\bar{\mathcal S}_{G_\alpha}$ is the set of points of the space of $G$ whose projection onto the space of $G_\alpha$ is in $\mathcal S_{G_\alpha}$. For a running intersection ordering $\bar e_1,\dots,\bar e_\kappa$ of the maximal edges, $G^+$ adds to $E$ the sets $N(\bar e_j)$, $j\ge 2$, of cardinality at least two (21). In the proof of Theorem 3 (§5.3), $\tilde e$ is the last maximal edge, $\bar p=N(\tilde e)$, $G^+$ adds $\bar p$ alone, $G_\alpha$ is the section hypergraph of $G^+$ induced by $\tilde e$, and $G_\omega$ the one induced by the union of the edges of $G^+$ outside $G_\alpha$.
--
--   These are the objects of every statement of the mission.
--
--   **Formalization Note** Nodes have a type `α` with decidable equality; a point is a function `z : α ⊕ Finset α → ℝ` (`Sum.inl v` is $z_v$, `Sum.inr e` is $z_e$), and every set attached to a hypergraph $H$ requires $z$ to vanish off the coordinates of $H$, so that polytopes of different hypergraphs live in one space; `restrict H z` is the projection onto the space of $H$. Orderings are lists and are 0-based ($N$ of position $0$ is $\emptyset$). The data of a running intersection inequality is the structure `RIData`: the neighbors are a set `K` of edges different from $e_0$, ordered by a duplicate-free list whose image under $e_0\cap\cdot$ is a running intersection ordering of $\tilde E$; the first sum of (5) runs over neighbors, so two neighbors with the same $u_k$ give the coefficient $-2$, as in (7). `MPRI` quantifies over every such datum: every center, neighbor set, ordering and choice of $u_k$. The number of components is that of the 2-section graph on the node set (isolated nodes count, loops connect nothing). `MPLP` has no row $z_v\ge 0$, as (8) has none. `addEdges` keeps only added sets with at least two nodes inside $V$; for $G^+$ this holds automatically. All counts are cast to `ℝ` before subtracting.
-- source:
--   Del Pia and Khajavirad, The running intersection relaxation of the multilinear polytope, Math. Oper. Res. 46 (2021), pp. 1008–1022, 1035: (1), (2)–(5), (8), MP^RI (p. 1014), §3.1 (p. 1018), kites and t-laminarity (pp. 1019–1020), I(e), ω(e), δ_e(v) and (20) (p. 1021), §3.3.2 (p. 1021), maximal edges and (21) (p. 1022), §5.3.1 (p. 1035)

import Mathlib

namespace RunIntersect.Tight

/-- A hypergraph without loops or parallel edges (§2, p. 1010): a finite node set `V` and a set `E`
of subsets of `V`, each of cardinality at least two. -/
structure Hypergraph (α : Type*) [DecidableEq α] where
  V : Finset α
  E : Finset (Finset α)
  edge_subset : ∀ e ∈ E, e ⊆ V
  two_le_card : ∀ e ∈ E, 2 ≤ e.card

variable {α : Type*} [DecidableEq α]

/-- The coordinates of `ℝ^{V+E}` inside the common space `α ⊕ Finset α → ℝ`: `inl v` for `v ∈ V`
and `inr e` for `e ∈ E`. -/
def Hypergraph.coords (H : Hypergraph α) : Finset (α ⊕ Finset α) :=
  H.V.image Sum.inl ∪ H.E.image Sum.inr

/-- Projection onto the space of `H`: keep the coordinates of `H`, set every other one to zero. -/
def restrict (H : Hypergraph α) (z : α ⊕ Finset α → ℝ) : α ⊕ Finset α → ℝ :=
  fun p => if p ∈ H.coords then z p else 0

/-- The multilinear set `S_H` of (1), p. 1008, pinned to zero off the coordinates of `H`. -/
def multilinearSet (H : Hypergraph α) : Set (α ⊕ Finset α → ℝ) :=
  {z | (∀ v ∈ H.V, z (Sum.inl v) = 0 ∨ z (Sum.inl v) = 1) ∧
    (∀ e ∈ H.E, z (Sum.inr e) = ∏ v ∈ e, z (Sum.inl v)) ∧
    ∀ p ∉ H.coords, z p = 0}

/-- The multilinear polytope `MP_H = conv S_H`. -/
def MP (H : Hypergraph α) : Set (α ⊕ Finset α → ℝ) :=
  convexHull ℝ (multilinearSet H)

/-- The standard linearization `MP^LP_H` of (8), p. 1014 (exactly the printed rows; no `z_v ≥ 0`
row), pinned to zero off the coordinates of `H`. -/
def MPLP (H : Hypergraph α) : Set (α ⊕ Finset α → ℝ) :=
  {z | (∀ v ∈ H.V, z (Sum.inl v) ≤ 1) ∧
    (∀ e ∈ H.E, 0 ≤ z (Sum.inr e) ∧
      (∑ v ∈ e, z (Sum.inl v)) - (e.card : ℝ) + 1 ≤ z (Sum.inr e) ∧
      ∀ v ∈ e, z (Sum.inr e) ≤ z (Sum.inl v)) ∧
    ∀ p ∉ H.coords, z p = 0}

/-- `⋃_{i<k} p_i` for a list `p_0, p_1, …` (0-based). -/
def prefixUnion (l : List (Finset α)) (k : ℕ) : Finset α :=
  (l.take k).foldr (· ∪ ·) ∅

/-- The set `N(p_k) = p_k ∩ ⋃_{i<k} p_i` of (3) (0-based; `Nset l 0 = ∅`). -/
def Nset (l : List (Finset α)) (k : ℕ) : Finset α :=
  l.getD k ∅ ∩ prefixUnion l k

/-- A running intersection ordering (2), p. 1010 (0-based): for each position `k ≥ 1` there is
`j < k` with `p_k ∩ ⋃_{i<k} p_i ⊆ p_j`. -/
def IsRIOrder (l : List (Finset α)) : Prop :=
  ∀ k, 0 < k → k < l.length → ∃ j < k, Nset l k ⊆ l.getD j ∅

/-- A multiset of sets has the running intersection property if some ordering of it is a running
intersection ordering. -/
def HasRIP (F : Multiset (Finset α)) : Prop :=
  ∃ l : List (Finset α), (l : Multiset (Finset α)) = F ∧ IsRIOrder l

/-- The 2-section graph on the node set `W` of the (multi)set of edges `F` (loops and parallel
edges allowed): two distinct nodes are adjacent iff some edge contains both. -/
def twoSection (W : Finset α) (F : Multiset (Finset α)) : SimpleGraph W where
  Adj u v := u ≠ v ∧ ∃ f ∈ F, (u : α) ∈ f ∧ (v : α) ∈ f
  symm := ⟨fun _ _ ⟨h, f, hf, hu, hv⟩ => ⟨h.symm, f, hf, hv, hu⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The number of connected components of the hypergraph `(W, F)` (§2.1, p. 1011): isolated nodes
count as components and loops connect nothing. -/
noncomputable def numComponents (W : Finset α) (F : Multiset (Finset α)) : ℕ :=
  Nat.card (twoSection W F).ConnectedComponent

/-- The data of a running intersection inequality (4)–(5), p. 1011: a center `e0 ∈ E`, a set `K`
of neighbors (edges different from `e0` and adjacent to it), an ordering `ord` of `K` such that
`e0 ∩ ord_0, e0 ∩ ord_1, …` is a running intersection ordering of `Ẽ`, and a node `u k ∈ N(e0 ∩ k)`
for every neighbor with `N(e0 ∩ k) ≠ ∅`. -/
structure RIData (H : Hypergraph α) where
  e0 : Finset α
  K : Finset (Finset α)
  ord : List (Finset α)
  u : Finset α → α
  he0 : e0 ∈ H.E
  hK : K ⊆ H.E.erase e0
  hadj : ∀ k ∈ K, (e0 ∩ k).Nonempty
  hnodup : ord.Nodup
  hord : ord.toFinset = K
  hri : IsRIOrder (ord.map (e0 ∩ ·))
  hu : ∀ k ∈ K, (Nset (ord.map (e0 ∩ ·)) (ord.idxOf k)).Nonempty →
    u k ∈ Nset (ord.map (e0 ∩ ·)) (ord.idxOf k)

namespace RIData

variable {H : Hypergraph α}

/-- `N(e0 ∩ e_k)`, the set (3) at the position of the neighbor `k` in the ordering. -/
def N (d : RIData H) (k : Finset α) : Finset α :=
  Nset (d.ord.map (d.e0 ∩ ·)) (d.ord.idxOf k)

/-- The left-hand side of the running intersection inequality (5). The first sum runs over the
neighbors `k` (two neighbors with the same `u_k` give the coefficient `-2`). -/
def lhs (d : RIData H) (z : α ⊕ Finset α → ℝ) : ℝ :=
  -(∑ k ∈ d.K.filter (fun k => (d.N k).Nonempty), z (Sum.inl (d.u k))) +
    (∑ v ∈ d.e0 \ d.K.biUnion id, z (Sum.inl v)) + (∑ k ∈ d.K, z (Sum.inr k)) -
    z (Sum.inr d.e0)

/-- The right-hand side `ω - 1` of (5), with `ω` the number of connected components of
`G̃ = (e0, Ẽ)`. -/
noncomputable def rhs (d : RIData H) : ℝ :=
  (numComponents d.e0 (d.K.val.map (d.e0 ∩ ·)) : ℝ) - 1

end RIData

/-- The running intersection relaxation `MP^RI_H` (p. 1014): `MP^LP_H` together with every running
intersection inequality (every center, neighbor set, ordering and choice of the nodes `u_k`). -/
def MPRI (H : Hypergraph α) : Set (α ⊕ Finset α → ℝ) :=
  MPLP H ∩ {z | ∀ d : RIData H, d.lhs z ≤ d.rhs}

/-- A β-cycle of length `t` (§3.1, p. 1018), 0-based: distinct nodes `v i` and distinct edges
`e i`, with `v i ∈ e j` iff `j = i` or `j = i - 1 (mod t)`, and `t ≥ 3`. -/
def IsBetaCycle (H : Hypergraph α) (t : ℕ) (v : Fin t → α) (e : Fin t → Finset α) : Prop :=
  3 ≤ t ∧ Function.Injective v ∧ Function.Injective e ∧ (∀ i, v i ∈ H.V) ∧ (∀ i, e i ∈ H.E) ∧
    ∀ i j, v i ∈ e j ↔ (j = i ∨ (j.val + 1) % t = i.val)

/-- A hypergraph is β-acyclic if it contains no β-cycle. -/
def IsBetaAcyclic (H : Hypergraph α) : Prop :=
  ∀ t v e, ¬ IsBetaCycle H t v e

/-- Kite-free (§3.3, pp. 1019–1020): no three edges `e0, e1, e2` with `|e0 ∩ e1 ∩ e2| ≥ 2`,
`(e0 ∩ e1) \ e2 ≠ ∅` and `(e0 ∩ e2) \ e1 ≠ ∅`. -/
def IsKiteFree (H : Hypergraph α) : Prop :=
  ¬ ∃ e0 ∈ H.E, ∃ e1 ∈ H.E, ∃ e2 ∈ H.E, 2 ≤ (e0 ∩ e1 ∩ e2).card ∧
    ((e0 ∩ e1) \ e2).Nonempty ∧ ((e0 ∩ e2) \ e1).Nonempty

/-- `t`-laminar (p. 1020): any two distinct edges meeting in at least `t` nodes are strictly
nested. -/
def IsLaminar (H : Hypergraph α) (t : ℕ) : Prop :=
  ∀ e1 ∈ H.E, ∀ e2 ∈ H.E, e1 ≠ e2 → t ≤ (e1 ∩ e2).card → e1 ⊂ e2 ∨ e2 ⊂ e1

/-- The section hypergraph of `H` induced by `W` (p. 1011): node set `W`, edges of `H` inside `W`. -/
def sectionHg (H : Hypergraph α) (W : Finset α) : Hypergraph α where
  V := W
  E := H.E.filter (· ⊆ W)
  edge_subset := fun _ he => (Finset.mem_filter.1 he).2
  two_le_card := fun e he => H.two_le_card e (Finset.mem_filter.1 he).1

/-- The subhypergraph `H_W` of `H` induced by `W` (p. 1018): node set `W`, edges `e ∩ W` with
`|e ∩ W| ≥ 2`. -/
def subHg (H : Hypergraph α) (W : Finset α) : Hypergraph α where
  V := W
  E := (H.E.image (· ∩ W)).filter (fun f => 2 ≤ f.card)
  edge_subset := fun f hf => by
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hf).1
    exact Finset.inter_subset_right
  two_le_card := fun _ hf => (Finset.mem_filter.1 hf).2

/-- `H` has no isolated node: every node lies in some edge. -/
def NoIsolated (H : Hypergraph α) : Prop :=
  ∀ v ∈ H.V, ∃ e ∈ H.E, v ∈ e

/-- The maximal edges of `H` (p. 1022): edges strictly contained in no other edge. -/
def maxEdges (H : Hypergraph α) : Finset (Finset α) :=
  H.E.filter (fun e => ∀ f ∈ H.E, ¬ e ⊂ f)

/-- The edge part `I(e) ∩ E` of `I(e)` (p. 1021): edges `f ⊂ e` contained in no edge `e' ⊂ e`. -/
def IE (H : Hypergraph α) (e : Finset α) : Finset (Finset α) :=
  H.E.filter (fun f => f ⊂ e ∧ ∀ e' ∈ H.E, e' ⊂ e → ¬ f ⊂ e')

/-- `I(e)` (p. 1021) as a set of coordinates: nodes `v ∈ e` lying in no edge `e' ⊂ e`, and the
edges of `IE H e`. -/
def Iset (H : Hypergraph α) (e : Finset α) : Finset (α ⊕ Finset α) :=
  (e.filter (fun v => ∀ e' ∈ H.E, e' ⊂ e → v ∉ e')).image Sum.inl ∪ (IE H e).image Sum.inr

/-- `ω(e)`: the number of connected components of `H_e = (e, I(e) ∩ E)`. -/
noncomputable def omegaE (H : Hypergraph α) (e : Finset α) : ℕ :=
  numComponents e (IE H e).val

/-- `δ_e(v)`: the number of edges of `H_e` containing `v`. -/
def deltaE (H : Hypergraph α) (e : Finset α) (v : α) : ℕ :=
  ((IE H e).filter (v ∈ ·)).card

/-- The system (20) of Proposition 6, p. 1021, pinned to zero off the coordinates of `H`.
"`p ⊄ f` for every `f ∈ E`" is read with strict inclusion: a node lying in no edge, or a maximal
edge. -/
noncomputable def system20 (H : Hypergraph α) : Set (α ⊕ Finset α → ℝ) :=
  {z | (∀ v ∈ H.V, z (Sum.inl v) ≤ 1) ∧
    (∀ v ∈ H.V, (∀ f ∈ H.E, v ∉ f) → 0 ≤ z (Sum.inl v)) ∧
    (∀ e ∈ H.E, (∀ f ∈ H.E, ¬ e ⊂ f) → 0 ≤ z (Sum.inr e)) ∧
    (∀ e ∈ H.E, ∀ p ∈ Iset H e, z (Sum.inr e) ≤ z p) ∧
    (∀ e ∈ H.E, (∑ v ∈ e, (1 - (deltaE H e v : ℝ)) * z (Sum.inl v)) +
      (∑ f ∈ IE H e, z (Sum.inr f)) - z (Sum.inr e) ≤ (omegaE H e : ℝ) - 1) ∧
    ∀ p ∉ H.coords, z p = 0}

/-- `S̄_{H}` (§3.3.2, p. 1021): the points of the space of `G` whose projection onto the space of
`H` lies in `S_H`. -/
def SBar (G H : Hypergraph α) : Set (α ⊕ Finset α → ℝ) :=
  {z | (∀ p ∉ G.coords, z p = 0) ∧ restrict H z ∈ multilinearSet H}

/-- `G` with the sets of `F` added as edges, keeping those of cardinality at least two that lie
inside `V` (for the auxiliary edges of (21) and §5.3 the second condition always holds). -/
def addEdges (G : Hypergraph α) (F : Finset (Finset α)) : Hypergraph α where
  V := G.V
  E := G.E ∪ F.filter (fun p => 2 ≤ p.card ∧ p ⊆ G.V)
  edge_subset := fun e he => by
    rcases Finset.mem_union.1 he with h | h
    · exact G.edge_subset e h
    · exact (Finset.mem_filter.1 h).2.2
  two_le_card := fun e he => by
    rcases Finset.mem_union.1 he with h | h
    · exact G.two_le_card e h
    · exact (Finset.mem_filter.1 h).2.1

/-- `G⁺ = (V, E⁺)` of (21), p. 1022, for an ordering `O = ē_1, …, ē_κ` of the maximal edges
(0-based: `j ∈ {2, …, κ}` becomes positions `1, …, κ - 1`). -/
def Gplus (G : Hypergraph α) (O : List (Finset α)) : Hypergraph α :=
  addEdges G (((Finset.range O.length).filter (1 ≤ ·)).image (Nset O))

/-- `p̄ = N(ẽ)` of §5.3.1, p. 1035: the set (3) of the last element `ẽ` of the ordering `O` of
the maximal edges. -/
def pbar (O : List (Finset α)) : Finset α :=
  Nset O (O.length - 1)

/-- `G⁺` of §5.3.1, p. 1035: `G` with `p̄` added as an edge when `|p̄| ≥ 2` (when `|p̄| ≤ 1`, or
`p̄ ∈ E`, nothing is added and `G⁺ = G`). -/
def GplusLast (G : Hypergraph α) (O : List (Finset α)) : Hypergraph α :=
  addEdges G {pbar O}

/-- `G_α` of §5.3.1: the section hypergraph of `G⁺` induced by the last maximal edge `ẽ`. -/
def GAlpha (G : Hypergraph α) (O : List (Finset α)) : Hypergraph α :=
  sectionHg (GplusLast G O) (O.getLastD ∅)

/-- `G_ω` of §5.3.1: the section hypergraph of `G⁺` induced by `⋃_{e ∈ E⁺ \ E(G_α)} e`. -/
def GOmega (G : Hypergraph α) (O : List (Finset α)) : Hypergraph α :=
  sectionHg (GplusLast G O) (((GplusLast G O).E \ (GAlpha G O).E).biUnion id)

end RunIntersect.Tight



-- Prove2me | Definitions.Def_RunIntersect_Strict_Setting
-- name    : RunIntersect_Strict_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T15:34:50.400977+00:00
-- url     : https://prove2.me/theorems/1c631e60-08f0-4dce-8c0b-edd471a24c2d
-- title:
--   §2–§3.2, pp. 1008–1019 — hypergraphs, S_G and MP_G (1), MP^LP_G (8), running intersection inequalities (5), MP^RI_G, β-cycles, subhypergraphs, L_V̄ (18) and proj_{G_V̄}, chordless cycles
-- statement:
--   This file fixes the objects of the mission, following Del Pia and Khajavirad (2021).
--
--   1. **Hypergraphs.** A hypergraph $G=(V,E)$ consists of a finite node set $V$ and a set $E$ of subsets of $V$, each of cardinality at least two (no loops, no parallel edges, as the paper assumes throughout). A node is *isolated* if it lies in no edge.
--   2. **Multilinear set and polytope.** The multilinear set of $G$ is
--   $$\mathcal S_G=\Big\{z\in\{0,1\}^{V+E}:\ z_e=\prod_{v\in e}z_v\ \ \forall e\in E\Big\},$$
--   and the multilinear polytope is $\mathrm{MP}_G=\operatorname{conv}\mathcal S_G$.
--   3. **Standard linearization (8).**
--   $$\mathrm{MP}^{\mathrm{LP}}_G=\Big\{z:\ z_v\le 1\ \forall v\in V;\ \ z_e\ge 0,\ z_e\ge \sum_{v\in e}z_v-|e|+1\ \forall e\in E;\ \ z_e\le z_v\ \forall e\in E,\ v\in e\Big\}.$$
--   There is no constraint $z_v\ge 0$, exactly as printed.
--   4. **Running intersection orderings (2)–(3).** An ordering $p_1,\dots,p_m$ of a multiset of sets is a running intersection ordering if for every $k\ge 2$ there is $j<k$ with $p_k\cap\bigcup_{i<k}p_i\subseteq p_j$; it induces $N(p_1)=\emptyset$ and $N(p_k)=p_k\cap\bigcup_{i<k}p_i$.
--   5. **Running intersection inequalities (4)–(5).** Given a center $e_0\in E$, a collection of distinct edges $e_k\ne e_0$, $k\in K$, each meeting $e_0$, a running intersection ordering of $\tilde E=\{e_0\cap e_k:k\in K\}$, and a node $u_k\in N(e_0\cap e_k)$ for each $k$ with $N(e_0\cap e_k)\neq\emptyset$, the running intersection inequality is
--   $$-\sum_{k\in K:\,N(e_0\cap e_k)\neq\emptyset}z_{u_k}+\sum_{v\in e_0\setminus\bigcup_{k\in K}e_k}z_v+\sum_{k\in K}z_{e_k}-z_{e_0}\le\omega-1,$$
--   where $\omega$ is the number of connected components of the hypergraph $\tilde G=(e_0,\tilde E)$ (loops and parallel edges allowed; an isolated node is a component).
--   6. **Running intersection relaxation.** $\mathrm{MP}^{\mathrm{RI}}_G$ is $\mathrm{MP}^{\mathrm{LP}}_G$ intersected with all running intersection inequalities (all centers, all neighbor sets, all orderings, all choices of the $u_k$).
--   7. **β-cycles.** A β-cycle of length $t\ge 3$ is a sequence $v_1,e_1,\dots,v_t,e_t,v_1$ of distinct nodes and distinct edges such that each $v_i$ belongs to $e_{i-1}$ and $e_i$ (indices mod $t$) and to no other $e_j$. $G$ is β-acyclic if it has no β-cycle.
--   8. **Subhypergraphs.** For $W\subseteq V$, $G_W$ has node set $W$ and edge set $\{e\cap W:e\in E,\ |e\cap W|\ge 2\}$.
--   9. **(18) and the projection.** $L_W=\{z: z_v=1\ \forall v\in V\setminus W\}$. For a choice of an edge $e'(f)\in E$ with $e'(f)\cap W=f$ for each edge $f$ of $G_W$, $\mathrm{proj}_{G_W}$ keeps $z_v$ ($v\in W$) and reads the coordinate of $f$ from $z_{e'(f)}$, projecting out every other variable.
--   10. **Chordless cycles.** For distinct nodes $v_1,\dots,v_t$, $t\ge3$, the chordless cycle has edges $\{v_i,v_{i+1}\}$ (indices mod $t$); the *enclosed* chordless cycle has in addition the edge $\{v_1,\dots,v_t\}$.
--
--   These are the objects in which every statement of the mission is phrased.
--
--   **Formalization Note** Points of $\mathbb R^{V+E}$ are functions $z:\alpha\oplus\mathrm{Finset}\,\alpha\to\mathbb R$ ($z(\mathrm{inl}\,v)=z_v$, $z(\mathrm{inr}\,e)=z_e$), and every polytope of $G$ is pinned to $0$ off the coordinates of $G$, so polytopes of different hypergraphs live in one space. Orderings and cycles are $0$-indexed; $N$ of a neighbor is read off its position in the ordering, and the first sum of (5) runs over the neighbors $k$ (two neighbors with the same $u_k$ contribute coefficient $-2$). $\omega$ is the number of connected components of the 2-section graph on $e_0$. The projection takes the choice $e'$ as an argument, so the lemmas are stated for every choice. The definitions coincide with those of the sibling missions of this series (sub-namespaces `Tight`, `Facet`).
-- source:
--   Del Pia and Khajavirad, The running intersection relaxation of the multilinear polytope, Math. Oper. Res. 46 (2021), doi:10.1287/moor.2021.1121, pp. 1008 (1), 1010–1011 (2)–(5), 1014 (8) and MP^RI, 1018 (β-cycles, subhypergraphs, e′(e)), 1019 (18) and proj, proof of Proposition 5

import Mathlib

namespace RunIntersect.Strict

/-- §2, p. 1010: a hypergraph without loops or parallel edges. `E` is a `Finset` (no parallel edges)
and every edge has at least two nodes (no loops). -/
structure Hypergraph (α : Type*) [DecidableEq α] where
  V : Finset α
  E : Finset (Finset α)
  edge_subset : ∀ e ∈ E, e ⊆ V
  two_le_card : ∀ e ∈ E, 2 ≤ e.card

variable {α : Type*} [DecidableEq α]

/-- The coordinates of `ℝ^{V+E}` inside the ambient space `α ⊕ Finset α → ℝ`:
`inl v` for a node `v ∈ V`, `inr e` for an edge `e ∈ E`. -/
def Hypergraph.coords (H : Hypergraph α) : Set (α ⊕ Finset α) :=
  {p | (∃ v ∈ H.V, p = Sum.inl v) ∨ ∃ e ∈ H.E, p = Sum.inr e}

/-- (1), p. 1008: the multilinear set `S_G`, pinned to zero off the coordinates of `H`. -/
def multilinearSet (H : Hypergraph α) : Set (α ⊕ Finset α → ℝ) :=
  {z | (∀ v ∈ H.V, z (Sum.inl v) = 0 ∨ z (Sum.inl v) = 1) ∧
       (∀ e ∈ H.E, z (Sum.inr e) = ∏ v ∈ e, z (Sum.inl v)) ∧
       ∀ p ∉ H.coords, z p = 0}

/-- p. 1008: the multilinear polytope `MP_G = conv S_G`. -/
def MP (H : Hypergraph α) : Set (α ⊕ Finset α → ℝ) :=
  convexHull ℝ (multilinearSet H)

/-- (8), p. 1014: the standard linearization `MP^LP_G`, exactly the printed system (no row `z_v ≥ 0`),
pinned to zero off the coordinates of `H`. -/
def MPLP (H : Hypergraph α) : Set (α ⊕ Finset α → ℝ) :=
  {z | (∀ v ∈ H.V, z (Sum.inl v) ≤ 1) ∧
       (∀ e ∈ H.E, 0 ≤ z (Sum.inr e) ∧
          (∑ v ∈ e, z (Sum.inl v)) - (e.card : ℝ) + 1 ≤ z (Sum.inr e) ∧
          ∀ v ∈ e, z (Sum.inr e) ≤ z (Sum.inl v)) ∧
       ∀ p ∉ H.coords, z p = 0}

/-- `⋃_{i<k} p_i` for a list `p_0, p_1, …` (0-based). -/
def prefixUnion (l : List (Finset α)) (k : ℕ) : Finset α :=
  (l.take k).foldr (· ∪ ·) ∅

/-- (2), p. 1010, 0-based: a running intersection ordering. For each position `k ≥ 1` there is
`j < k` with `p_k ∩ ⋃_{i<k} p_i ⊆ p_j`. -/
def IsRIOrder (l : List (Finset α)) : Prop :=
  ∀ k (hk : k < l.length), 0 < k → ∃ j, ∃ hj : j < k, l[k] ∩ prefixUnion l k ⊆ l[j]'(by omega)

/-- (3), p. 1010, 0-based: `N(p_0) = ∅`, `N(p_k) = p_k ∩ ⋃_{i<k} p_i`. -/
def Nset (l : List (Finset α)) (k : ℕ) : Finset α :=
  (l.getD k ∅) ∩ prefixUnion l k

/-- The 2-section graph on the node set `W` of a multiset `F` of subsets (loops and parallel edges
allowed): two distinct nodes are adjacent iff some member of `F` contains both. -/
def twoSection (W : Finset α) (F : Multiset (Finset α)) : SimpleGraph W where
  Adj u v := u ≠ v ∧ ∃ f ∈ F, (u : α) ∈ f ∧ (v : α) ∈ f
  symm := by
    constructor
    intro u v ⟨h, f, hf, hu, hv⟩
    exact ⟨Ne.symm h, f, hf, hv, hu⟩
  loopless := by
    constructor
    intro u h
    exact h.1 rfl

/-- p. 1011: the number of connected components of the hypergraph `(W, F)`. Two distinct nodes lie in
the same component iff they are joined by a chain, i.e. by a path of the 2-section graph; an isolated
node is its own component. -/
noncomputable def numComponents (W : Finset α) (F : Multiset (Finset α)) : ℕ :=
  Nat.card (twoSection W F).ConnectedComponent

/-- (3)–(4): `N(e₀ ∩ k)` for a neighbor `k`, computed from its position in the ordering `ord` of the
neighbors, i.e. in the ordering `e₀ ∩ ord[0], e₀ ∩ ord[1], …` of `Ẽ`. -/
def riN (e0 : Finset α) (ord : List (Finset α)) (k : Finset α) : Finset α :=
  Nset (ord.map (e0 ∩ ·)) (ord.idxOf k)

/-- (4)–(5), p. 1011: the data of a running intersection inequality of `H`: a center `e0 ∈ E`, a set
`K` of distinct neighbors (edges other than `e0` adjacent to `e0`), an ordering `ord` of `K` such that
`e0 ∩ ord[0], e0 ∩ ord[1], …` is a running intersection ordering of `Ẽ`, and a choice `u k ∈ N(e₀ ∩ k)`
for every neighbor with `N(e₀ ∩ k) ≠ ∅`. -/
structure RIData (H : Hypergraph α) where
  e0 : Finset α
  K : Finset (Finset α)
  ord : List (Finset α)
  u : Finset α → α
  e0_mem : e0 ∈ H.E
  K_sub : K ⊆ H.E.erase e0
  K_adj : ∀ k ∈ K, (e0 ∩ k).Nonempty
  ord_nodup : ord.Nodup
  ord_toFinset : ord.toFinset = K
  ord_RI : IsRIOrder (ord.map (e0 ∩ ·))
  u_mem : ∀ k ∈ K, (riN e0 ord k).Nonempty → u k ∈ riN e0 ord k

/-- Left-hand side of (5):
`− ∑_{k ∈ K : N(e₀∩e_k) ≠ ∅} z_{u_k} + ∑_{v ∈ e₀ ∖ ⋃_k e_k} z_v + ∑_{k ∈ K} z_{e_k} − z_{e₀}`. -/
def RIData.lhs {H : Hypergraph α} (d : RIData H) (z : α ⊕ Finset α → ℝ) : ℝ :=
  -(∑ k ∈ d.K.filter (fun k => (riN d.e0 d.ord k).Nonempty), z (Sum.inl (d.u k)))
    + (∑ v ∈ d.e0 \ d.K.biUnion id, z (Sum.inl v))
    + (∑ k ∈ d.K, z (Sum.inr k)) - z (Sum.inr d.e0)

/-- Right-hand side of (5): `ω − 1`, with `ω` the number of connected components of `G̃ = (e₀, Ẽ)`. -/
noncomputable def RIData.rhs {H : Hypergraph α} (d : RIData H) : ℝ :=
  (numComponents d.e0 (d.K.val.map (d.e0 ∩ ·)) : ℝ) - 1

/-- p. 1014: the running intersection relaxation `MP^RI_G`: `MP^LP_G` together with every running
intersection inequality (every center, neighbor set, ordering and choice of the `u_k`). -/
def MPRI (H : Hypergraph α) : Set (α ⊕ Finset α → ℝ) :=
  MPLP H ∩ {z | ∀ d : RIData H, d.lhs z ≤ d.rhs}

/-- §3.1, p. 1018, 0-based: `v 0, e 0, v 1, e 1, …, v (t-1), e (t-1), v 0` is a β-cycle of length `t`:
`t ≥ 3`, distinct nodes, distinct edges, and `v i ∈ e j` iff `j = i` or `j = i − 1 (mod t)`. -/
def IsBetaCycle (H : Hypergraph α) (t : ℕ) (v : Fin t → α) (e : Fin t → Finset α) : Prop :=
  3 ≤ t ∧ Function.Injective v ∧ Function.Injective e ∧ (∀ i, v i ∈ H.V) ∧ (∀ i, e i ∈ H.E) ∧
    ∀ i j, v i ∈ e j ↔ (j = i ∨ (j.val + 1) % t = i.val)

/-- §3.1, p. 1018: `H` is β-acyclic if it contains no β-cycle. -/
def IsBetaAcyclic (H : Hypergraph α) : Prop :=
  ∀ t v e, ¬ IsBetaCycle H t v e

/-- No node of `H` is isolated: every node lies in some edge. -/
def NoIsolated (H : Hypergraph α) : Prop :=
  ∀ v ∈ H.V, ∃ e ∈ H.E, v ∈ e

/-- §3.1, p. 1018: the subhypergraph `G_W` induced by `W`: node set `W`, edge set
`{e ∩ W : e ∈ E, |e ∩ W| ≥ 2}` (equal traces collapse to one edge). -/
def subHg (H : Hypergraph α) (W : Finset α) : Hypergraph α where
  V := W
  E := (H.E.image (· ∩ W)).filter (fun f => 2 ≤ f.card)
  edge_subset := by
    intro f hf
    simp only [Finset.mem_filter, Finset.mem_image] at hf
    obtain ⟨⟨e, -, rfl⟩, -⟩ := hf
    exact Finset.inter_subset_right
  two_le_card := fun f hf => (Finset.mem_filter.mp hf).2

/-- (18), p. 1019: `L_W = {z : z_v = 1 for all v ∈ V ∖ W}`. -/
def Lset (H : Hypergraph α) (W : Finset α) : Set (α ⊕ Finset α → ℝ) :=
  {z | ∀ v ∈ H.V \ W, z (Sum.inl v) = 1}

/-- p. 1019: `proj_{G_W}`, for a choice `ep` of `e′(f)` (an edge of `G` with `e′(f) ∩ W = f`) for every
edge `f` of `G_W`: keep `z_v` for `v ∈ W` and read the coordinate of `f` from `z_{e′(f)}`; every other
coordinate is projected out (set to zero, the pin of `G_W`). -/
def projSub (H : Hypergraph α) (W : Finset α) (ep : Finset α → Finset α)
    (z : α ⊕ Finset α → ℝ) : α ⊕ Finset α → ℝ :=
  fun p => match p with
    | Sum.inl v => if v ∈ W then z (Sum.inl v) else 0
    | Sum.inr f => if f ∈ (subHg H W).E then z (Sum.inr (ep f)) else 0

/-- The successor `i + 1 (mod t)` on `Fin t`. -/
def cycSucc {t : ℕ} (i : Fin t) : Fin t :=
  ⟨(i.val + 1) % t, Nat.mod_lt _ i.pos⟩

theorem cycSucc_ne {t : ℕ} (ht : 3 ≤ t) (i : Fin t) : i ≠ cycSucc i := by
  intro h
  have h' : i.val = (i.val + 1) % t := congrArg Fin.val h
  rcases Nat.lt_or_ge (i.val + 1) t with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at h'
    omega
  · have : i.val + 1 = t := by omega
    rw [this, Nat.mod_self] at h'
    omega

/-- p. 1019: the chordless cycle on the distinct nodes `v 0, …, v (t-1)`, `t ≥ 3`, as a hypergraph:
node set `{v i}`, edges `{v i, v (i+1 mod t)}`. -/
def cycleHg (t : ℕ) (v : Fin t → α) (ht : 3 ≤ t) (hv : Function.Injective v) : Hypergraph α where
  V := Finset.univ.image v
  E := Finset.univ.image (fun i => ({v i, v (cycSucc i)} : Finset α))
  edge_subset := by
    intro f hf
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hf
    obtain ⟨i, rfl⟩ := hf
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  two_le_card := by
    intro f hf
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hf
    obtain ⟨i, rfl⟩ := hf
    rw [Finset.card_pair (hv.ne (cycSucc_ne ht i))]

/-- p. 1019: the chordless cycle `cycleHg t v` enclosed by the edge `{v 0, …, v (t-1)}`. -/
def enclosedCycleHg (t : ℕ) (v : Fin t → α) (ht : 3 ≤ t) (hv : Function.Injective v) :
    Hypergraph α where
  V := Finset.univ.image v
  E := insert (Finset.univ.image v) (cycleHg t v ht hv).E
  edge_subset := by
    intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact subset_rfl
    · exact (cycleHg t v ht hv).edge_subset f hf
  two_le_card := by
    intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · rw [Finset.card_image_of_injective _ hv, Finset.card_univ, Fintype.card_fin]
      omega
    · exact (cycleHg t v ht hv).two_le_card f hf

end RunIntersect.Strict



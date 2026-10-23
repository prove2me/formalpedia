-- Prove2me | Definitions.Def_HyperMatchDelay_Batching_Model
-- name    : HyperMatchDelay_Batching_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:20.067998+00:00
-- url     : https://prove2.me/theorems/bdaad8cb-2116-46f4-a74d-adbd0e624413
-- title:
--   Definitions 1, 8, 10, 18 and Algorithms 1, 2, 5, pp. 2–7, 14–19 — shareability hypergraphs, matchings, Greedy, Depth-k Greedy and Randomized-Batching
-- statement:
--   This file sets up the model of online hypergraph matching with delays and the algorithm Randomized-Batching with subroutine Depth-k Greedy.
--
--   **Hypergraphs and matchings.** Vertices are natural numbers; a hyperedge $e$ is a finite set of vertices, an edge set $E$ is a finite family of hyperedges, and $w$ assigns a real weight to every hyperedge. The **diameter** of a non-empty hyperedge is $\mathrm{diam}(e) = \max e - \min e = \max_{i,j \in e}|i-j|$. The weight of a set of edges $M$ is $w(M) = \sum_{e \in M} w(e)$, and $M$ is a **matching** of $E$ if $M \subseteq E$ and its edges are pairwise disjoint (Definitions 8 and 10).
--
--   **Shareability hypergraph** (Definition 1). For parameters $(n, d, k)$, the hypergraph $(V, E, w)$ with $V = [n] = \{1,\dots,n\}$ (vertex $i$ arrives at time $i$) is a shareability hypergraph if every $e \in E$ is a non-empty subset of $[n]$ with
--   $$\mathrm{diam}(e) < d,\qquad |e| \le k,\qquad w(e) \ge 0 .$$
--
--   **Greedy** (Algorithm 5). Given a finite edge set $S$, list its edges in non-increasing order of weight, ties broken arbitrarily, and scan the list, keeping each edge that is disjoint from all edges kept so far. Arbitrary tie-breaking is modelled by an ordering oracle $\sigma$: for every $S$, $\sigma(S)$ lists each edge of $S$ exactly once in non-increasing weight order.
--
--   **Depth-k Greedy** (Algorithm 2, Definition 18). For a batch with ordered vertex set $B$ and edge set $E_B$, let $L$ be the $k$ smallest and $R$ the $k$ largest vertices of $B$ (all of $B$ if $|B| \le k$), and let $\mathcal M_{L,R}$ be the matchings of $E_B$ all of whose edges meet both $L$ and $R$; it always contains $\emptyset$. For $M \in \mathcal M_{L,R}$, let $\widetilde M = \mathrm{Greedy}$ run on the edges of $E_B$ avoiding every vertex matched by $M$. Depth-k Greedy returns $M_{i^*} \cup \widetilde M_{i^*}$ for a maximizer $M_{i^*}$ of $w(M \cup \widetilde M)$.
--
--   **Batches and Randomized-Batching** (Algorithm 1; proof of Theorem 2). For a shift $z \in \{0,\dots,d-1\}$ and an index $i \in \mathbb Z$ the window is
--   $$V_{z,i} = \{\, v \in [n] : z + id \le v \le z + (i+1)d - 1 \,\},$$
--   the batch edges are $E_{z,i} = \{e \in E : e \subseteq V_{z,i}\}$, and $E_z = \bigcup_i E_{z,i}$. With $i$ ranging over $\{-1, 0, \dots, \lfloor n/d \rfloor\}$, Randomized-Batching with realized shift $Z = z$ returns $M_z = \bigcup_i \mathrm{DepthKGreedy}(V_{z,i}, E_{z,i})$.
--
--   These objects are the vocabulary of every statement of the mission.
--
--   **Formalization Note** Hyperedges are required to be non-empty (the paper never says so; a hyperedge is a request group). The windows are indexed by all $i \in \{-1,\dots,\lfloor n/d\rfloor\}$ and are disjoint, so the first $z$ requests form a batch of their own and the last batch does not overlap the previous one; the paper's Algorithm 1 and Appendix B.3 index these boundary batches loosely. Definition 18's side condition $L \cap R = \emptyset$ is not imposed (it fails when the batch has fewer than $2k$ vertices and no argument uses it). The maximizer in Depth-k Greedy is chosen by `Classical.choose`; every statement of the mission concerns its weight or matching property, which all maximizers share. The expectation over the uniform shift $Z$ is written as the average $\frac1d\sum_{z=0}^{d-1}$.
-- source:
--   Pavone, Saberi, Schiffer & Tsao, Online Hypergraph Matching with Delays, arXiv:2009.12022v1, pp. 2–3, 5–7, 14–15, 17–19, Definitions 1, 2, 8, 10, 13, 18, Algorithms 1, 2, 5

import Mathlib

namespace HyperMatchDelay.Batching

/-- Definition 1 / Definition 13 (pp. 2, 14): the diameter `max_{i,j ∈ e} |i - j|` of a hyperedge
`e ⊆ ℕ`, i.e. its largest minus its smallest vertex (`0` for the empty set, which never occurs
for an edge of a shareability hypergraph). -/
def diam (e : Finset ℕ) : ℕ :=
  if h : e.Nonempty then e.max' h - e.min' h else 0

/-- Definition 1 (p. 2): `(V, E, w)` with `V = [n] = {1, …, n}` is a shareability hypergraph with
parameters `(n, d, k)`: every hyperedge is a non-empty subset of `[n]` of diameter `< d` and of
cardinality `≤ k`, with non-negative weight. (Non-emptiness of hyperedges is the field's standing
convention; the paper does not state it.) -/
def IsShareability (n d k : ℕ) (E : Finset (Finset ℕ)) (w : Finset ℕ → ℝ) : Prop :=
  ∀ e ∈ E, e ⊆ Finset.Icc 1 n ∧ e.Nonempty ∧ diam e < d ∧ e.card ≤ k ∧ 0 ≤ w e

/-- Definition 10 (p. 14): `M` is a matching in the hypergraph with edge set `E`: `M ⊆ E` and the
edges of `M` are pairwise disjoint. -/
def IsMatching (E M : Finset (Finset ℕ)) : Prop :=
  M ⊆ E ∧ (M : Set (Finset ℕ)).PairwiseDisjoint id

/-- Definition 8 (p. 14): the weight `w(M) = ∑_{e ∈ M} w(e)` of a set of edges. -/
def weight (w : Finset ℕ → ℝ) (M : Finset (Finset ℕ)) : ℝ :=
  ∑ e ∈ M, w e

/-- The vertex set `V(M)` matched by a set of edges `M` (Appendix B.3, p. 19). -/
def vertices (M : Finset (Finset ℕ)) : Finset ℕ :=
  M.biUnion id

/-- Algorithm 5, line 4 (p. 15): `σ` is a weight-sorted ordering oracle: for every finite edge set
`S`, `σ S` lists every edge of `S` exactly once, in non-increasing order of weight. Ties are
arbitrary, and may be broken differently in every call. -/
def IsSortedOrder (w : Finset ℕ → ℝ) (σ : Finset (Finset ℕ) → List (Finset ℕ)) : Prop :=
  ∀ S, (σ S).Nodup ∧ (σ S).toFinset = S ∧ (σ S).Pairwise (fun a b => w b ≤ w a)

/-- Algorithm 5, lines 6–7 (p. 15): add the edge `e` to `M` if `M ∪ {e}` is still a matching. -/
def greedyStep (M : Finset (Finset ℕ)) (e : Finset ℕ) : Finset (Finset ℕ) :=
  if ∀ f ∈ M, Disjoint e f then insert e M else M

/-- Algorithm 5 (`Greedy`, p. 15): scan the edges of `S` in the sorted order `σ S` and keep each
edge that is disjoint from every edge kept so far. -/
def greedy (σ : Finset (Finset ℕ) → List (Finset ℕ)) (S : Finset (Finset ℕ)) :
    Finset (Finset ℕ) :=
  (σ S).foldl greedyStep ∅

/-- Algorithm 2, line 3 (p. 7): the first `k` vertices of the ordered vertex set `B`
(the `k` smallest elements; all of `B` if `B` has at most `k` elements). -/
def firstK (B : Finset ℕ) (k : ℕ) : Finset ℕ :=
  B.filter (fun v => (B.filter (fun u => u < v)).card < k)

/-- Algorithm 2, line 4 (p. 7): the last `k` vertices of the ordered vertex set `B`
(the `k` largest elements; all of `B` if `B` has at most `k` elements). -/
def lastK (B : Finset ℕ) (k : ℕ) : Finset ℕ :=
  B.filter (fun v => (B.filter (fun u => v < u)).card < k)

/-- Definition 18, item 2 (p. 19): every edge of `M` meets both `L` and `R`. -/
def IsRestricted (L R : Finset ℕ) (M : Finset (Finset ℕ)) : Prop :=
  ∀ e ∈ M, (e ∩ L).Nonempty ∧ (e ∩ R).Nonempty

open Classical in
/-- Definition 18 (p. 19): `M_{L,R}`, the matchings in the hypergraph with edge set `EB` all of
whose edges meet both `L` and `R`. (The paper's side condition `L ∩ R = ∅` is not imposed.) -/
noncomputable def restrictedMatchings (EB : Finset (Finset ℕ)) (L R : Finset ℕ) :
    Finset (Finset (Finset ℕ)) :=
  EB.powerset.filter (fun M => IsMatching EB M ∧ IsRestricted L R M)

theorem empty_mem_restrictedMatchings (EB : Finset (Finset ℕ)) (L R : Finset ℕ) :
    ∅ ∈ restrictedMatchings EB L R := by
  classical
  unfold restrictedMatchings
  exact Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset EB,
    ⟨Finset.empty_subset EB, by rw [Finset.coe_empty]; exact Set.pairwiseDisjoint_empty⟩,
    fun e he => absurd he (Finset.notMem_empty e)⟩

/-- Algorithm 2, line 9 (p. 7): `Greedy((V \ V(M), E))`, Greedy run on the edges of `EB` that avoid
every vertex matched by `M`. -/
def greedyAvoiding (σ : Finset (Finset ℕ) → List (Finset ℕ)) (EB M : Finset (Finset ℕ)) :
    Finset (Finset ℕ) :=
  greedy σ (EB.filter (fun e => Disjoint e (vertices M)))

/-- Algorithm 2, line 10 (p. 7): a matching `M_{i*} ∈ M_{L,R}` maximizing
`w(M ∪ Greedy((V \ V(M), E)))`, with `L`, `R` the first and last `k` vertices of `B`. -/
noncomputable def depthKChoice (σ : Finset (Finset ℕ) → List (Finset ℕ)) (w : Finset ℕ → ℝ)
    (k : ℕ) (B : Finset ℕ) (EB : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  Classical.choose (Finset.exists_max_image (restrictedMatchings EB (firstK B k) (lastK B k))
    (fun M => weight w (M ∪ greedyAvoiding σ EB M))
    ⟨∅, empty_mem_restrictedMatchings EB _ _⟩)

/-- Algorithm 2 (`Depth-k Greedy`, p. 7) on the batch with ordered vertex set `B` and edge set
`EB`: returns `M_{i*} ∪ Greedy((V \ V(M_{i*}), E))`. -/
noncomputable def depthKGreedy (σ : Finset (Finset ℕ) → List (Finset ℕ)) (w : Finset ℕ → ℝ)
    (k : ℕ) (B : Finset ℕ) (EB : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  depthKChoice σ w k B EB ∪ greedyAvoiding σ EB (depthKChoice σ w k B EB)

/-- Proof of Theorem 2, p. 6 / Appendix B.3, p. 17: the batch window
`V_{z,i} = {z + i d, …, z + (i + 1) d - 1} ∩ [n]` (computed in `ℤ`, `i ∈ ℤ`). -/
def window (n d z : ℕ) (i : ℤ) : Finset ℕ :=
  (Finset.Icc 1 n).filter
    (fun v => (z : ℤ) + i * d ≤ (v : ℤ) ∧ (v : ℤ) ≤ (z : ℤ) + (i + 1) * d - 1)

/-- `E_{z,i} = {e ∈ E : e ⊆ V_{z,i}}` (p. 6). -/
def batchEdges (E : Finset (Finset ℕ)) (n d z : ℕ) (i : ℤ) : Finset (Finset ℕ) :=
  E.filter (fun e => e ⊆ window n d z i)

/-- The batch indices `i ∈ {-1, 0, …, ⌊n/d⌋}`; for `z < d` their windows cover `[n]`. -/
noncomputable def batchIndices (n d : ℕ) : Finset ℤ :=
  Finset.Icc (-1) ((n : ℤ) / (d : ℤ))

/-- `E_z = ⋃_i E_{z,i}` (p. 6). -/
noncomputable def shiftEdges (E : Finset (Finset ℕ)) (n d z : ℕ) : Finset (Finset ℕ) :=
  (batchIndices n d).biUnion (fun i => batchEdges E n d z i)

/-- Algorithm 1 (`Randomized-Batching`, p. 5) with subroutine `A = Depth-k Greedy`, for the
realized shift `Z = z`: `M_z = ⋃_i DepthKGreedy(W_{z,i})`. -/
noncomputable def randomizedBatching (σ : Finset (Finset ℕ) → List (Finset ℕ))
    (w : Finset ℕ → ℝ) (n d k : ℕ) (E : Finset (Finset ℕ)) (z : ℕ) : Finset (Finset ℕ) :=
  (batchIndices n d).biUnion
    (fun i => depthKGreedy σ w k (window n d z i) (batchEdges E n d z i))

end HyperMatchDelay.Batching



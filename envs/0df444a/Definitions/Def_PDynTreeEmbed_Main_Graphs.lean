-- Prove2me | Definitions.Def_PDynTreeEmbed_Main_Graphs
-- name    : PDynTreeEmbed_Main_Graphs
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:30:27.743694+00:00
-- url     : https://prove2.me/theorems/6b6abb31-70ea-47ba-9d1c-3880204f22a2
-- title:
--   Weighted graphs, distances, balls, E(A, B), volume, trees on a node set, and partially dynamic update sequences
-- statement:
--   A **weighted graph** on a vertex set $V$ is a simple undirected graph together with a weight $w(e)\in\mathbb Z_{\ge 0}$ on every edge. The **weight of a walk** is the sum of the weights of its edges, and the **distance** $\mathrm{dist}_G(u,v)\in\mathbb Z_{\ge0}\cup\{\infty\}$ is the least weight of a walk from $u$ to $v$ ($\infty$ if there is none). For a vertex $w$ and a nonempty set $Z$, $\mathrm{dist}_G(w,Z)=\min_{z\in Z}\mathrm{dist}_G(w,z)$, and for a set $X$, $\mathrm{dist}_G(X,u)=\min_{x\in X}\mathrm{dist}_G(x,u)$.
--
--   The **ball** of radius $R\in\mathbb R$ around $v$ is $B_G(v,R)=\{u\in V:\mathrm{dist}_G(v,u)\le R\}$, and around a set $X$ it is $B_G(X,R)=\{u:\mathrm{dist}_G(X,u)\le R\}$. For sets $A,B$, $E(A,B)$ is the set of edges with one endpoint in $A$ and the other in $B$. The **degree** of a vertex is its number of incident edges and the **volume** of a set is the sum of the degrees of its vertices.
--
--   A weighted graph $T$ is a **tree on the node set $S$** if every edge of $T$ joins two nodes of $S$ and the graph induced on $S$ is connected and acyclic.
--
--   **Partially dynamic instances.** The vertex set is $V=\{0,\dots,n-1\}$. An update inserts a new edge $\{u,v\}$ ($u\ne v$) with an integer weight $c$, or deletes a present edge. An **instance** with weight bound $W$ is an initial graph $G^{(0)}$ with integer weights in $[1,W]$, a kind (insertions only or deletions only), and a finite list of updates of that kind, every inserted weight in $[1,W]$, such that every graph $G^{(0)},\dots,G^{(T)}$ along the sequence is connected. Here $G^{(t)}$ is the graph after the first $t$ updates, and $m$ is the number of edges present initially or inserted. The **union graph** is the graph holding every edge ever present: the final graph for insertions, the initial graph for deletions.
--
--   **Formalization Note.** `WGraph α` is a `SimpleGraph α` with a weight `Sym2 α → ℕ`; no positivity, finiteness or connectivity is built in, and these are hypotheses where the paper assumes them. `dist` takes values in `ℕ∞`; `rdist` is its real value (used on connected graphs only). Balls compare the real radius with the finite distance. `log2` is `Real.logb 2`. Permutations of `Fin n` carry the discrete σ-algebra.
-- source:
--   Dorkofikis, Probst Gutenberg, Tight Low-Diameter Decompositions and Tree Embeddings in Partially Dynamic Graphs, STOC 2027 submission (manuscript sha256 bf7ba5b2…), pp. 1 (footnote 1), 2 (§1), 13 (§3)

import Mathlib

namespace PDynTreeEmbed.Main

/-! # Weighted graphs, distances, balls, trees, and partially dynamic update sequences

Dorkofikis, Probst Gutenberg, *Tight Low-Diameter Decompositions and Tree Embeddings in Partially
Dynamic Graphs*, STOC 2027 submission (manuscript sha256 bf7ba5b2…), p. 1 footnote 1, p. 2 (§1),
p. 13 (§3 Preliminaries).

**Formalization Note.** A weighted graph on a vertex type `α` is a simple graph together with a
natural-number weight on unordered pairs, of which only the values on edges matter. No positivity,
finiteness or connectivity is built in; those are hypotheses where the paper assumes them. The
distance `dist u v ∈ ℕ ∪ {∞}` is the infimum, over all walks from `u` to `v`, of the sum of the edge
weights along the walk, and `∞` when no walk exists. `rdist` is its value as a real number (used only
on connected graphs, where it is finite). The input graph of the paper has vertex set `Fin n`.
A partially dynamic update sequence is a list of updates of one kind: insertions of a new edge with a
weight, or deletions of a present edge. -/

/-- A weighted undirected graph on the vertex type `α`: a simple graph `adj` and a weight
`wt : Sym2 α → ℕ` on unordered pairs (only its values on edges matter). -/
structure WGraph (α : Type) where
  /-- The underlying simple graph. -/
  adj : SimpleGraph α
  /-- The weight of an unordered pair. -/
  wt : Sym2 α → ℕ

namespace WGraph

variable {α : Type}

/-- The weight of a walk: the sum of the weights of its edges, with multiplicity. -/
def walkWeight (G : WGraph α) {u v : α} (p : G.adj.Walk u v) : ℕ :=
  (p.edges.map G.wt).sum

/-- The shortest-path distance `dist_G(u, v) ∈ ℕ ∪ {∞}`: the infimum of the weights of all walks
from `u` to `v` (`∞` if there is none). -/
noncomputable def dist (G : WGraph α) (u v : α) : ℕ∞ :=
  ⨅ p : G.adj.Walk u v, (G.walkWeight p : ℕ∞)

/-- `dist_G(u, v)` as a real number (its value when finite; used on connected graphs only). -/
noncomputable def rdist (G : WGraph α) (u v : α) : ℝ :=
  ((G.dist u v).toNat : ℝ)

/-- `dist_G(w, Z) = min_{z ∈ Z} dist_G(w, z)` (p. 14), in `ℕ ∪ {∞}` (`∞` for `Z = ∅`). -/
noncomputable def distTo (G : WGraph α) (w : α) (Z : Finset α) : ℕ∞ :=
  ⨅ z ∈ Z, G.dist w z

/-- `dist_G(X, u) = min_{x ∈ X} dist_G(x, u)`, in `ℕ ∪ {∞}` (`∞` for `X = ∅`). -/
noncomputable def distFrom (G : WGraph α) (X : Finset α) (u : α) : ℕ∞ :=
  ⨅ x ∈ X, G.dist x u

open Classical in
/-- The ball `B_G(v, R) = {u ∈ V : dist_G(v, u) ≤ R}` (p. 13), for a real radius `R`. -/
noncomputable def ball [Fintype α] (G : WGraph α) (v : α) (R : ℝ) : Finset α :=
  Finset.univ.filter fun u => G.dist v u ≠ ⊤ ∧ ((G.dist v u).toNat : ℝ) ≤ R

open Classical in
/-- The ball `B_G(X, R) = {u ∈ V : dist_G(X, u) ≤ R}` around a vertex set `X` (p. 13). -/
noncomputable def ballSet [Fintype α] (G : WGraph α) (X : Finset α) (R : ℝ) : Finset α :=
  Finset.univ.filter fun u => G.distFrom X u ≠ ⊤ ∧ ((G.distFrom X u).toNat : ℝ) ≤ R

/-- `E(A, B)`: the edges with one endpoint in `A` and the other in `B` (p. 13), as unordered
pairs. -/
def edgesBetween (G : WGraph α) (A B : Set α) : Set (Sym2 α) :=
  {e | e ∈ G.adj.edgeSet ∧ ∃ u ∈ A, ∃ v ∈ B, e = s(u, v)}

/-- Every edge weight is an integer in `[1, W]` (p. 13: `w : E → [1, W]`, integral). -/
def HasWeightsIn (G : WGraph α) (W : ℕ) : Prop :=
  ∀ e ∈ G.adj.edgeSet, 1 ≤ G.wt e ∧ G.wt e ≤ W

/-- Every edge weight is a positive integer. -/
def HasPosWeights (G : WGraph α) : Prop :=
  ∀ e ∈ G.adj.edgeSet, 1 ≤ G.wt e

/-- The degree of `v`: its number of incident edges. -/
noncomputable def deg (G : WGraph α) (v : α) : ℕ :=
  (G.adj.neighborSet v).ncard

/-- The volume `vol(S) = Σ_{v ∈ S} deg(v)` of a vertex set. -/
noncomputable def vol (G : WGraph α) (S : Finset α) : ℕ :=
  ∑ v ∈ S, G.deg v

/-- `T` is a tree on the node set `S`: every edge of `T` has both endpoints in `S`, and the graph
induced on `S` is a tree (connected, nonempty and acyclic). -/
def IsTreeOn (T : WGraph α) (S : Set α) : Prop :=
  (∀ e ∈ T.adj.edgeSet, ∀ x ∈ e, x ∈ S) ∧ (T.adj.induce S).IsTree

end WGraph

/-- The kind of a partially dynamic update sequence: edge insertions only (incremental) or edge
deletions only (decremental). -/
inductive Kind where
  | incr
  | decr
  deriving DecidableEq

/-- An edge update on `Fin n`: insert the edge `{u, v}` with weight `c`, or delete the edge
`{u, v}`. -/
inductive Upd (n : ℕ) where
  | ins (u v : Fin n) (c : ℕ)
  | del (u v : Fin n)

/-- Whether an update is an insertion. -/
def Upd.isIns {n : ℕ} : Upd n → Bool
  | .ins _ _ _ => true
  | .del _ _ => false

/-- The graph after an update. An insertion adds the edge and sets its weight; a deletion removes
the edge. -/
def Upd.apply {n : ℕ} (G : WGraph (Fin n)) : Upd n → WGraph (Fin n)
  | .ins u v c => ⟨G.adj ⊔ SimpleGraph.edge u v, Function.update G.wt s(u, v) c⟩
  | .del u v => ⟨G.adj.deleteEdges {s(u, v)}, G.wt⟩

/-- `G^(t)`: the graph after the first `t` updates of `σ`, starting from `G^(0) = G₀`. -/
def graphAt {n : ℕ} (G₀ : WGraph (Fin n)) (σ : List (Upd n)) (t : ℕ) : WGraph (Fin n) :=
  (σ.take t).foldl Upd.apply G₀

/-- A legal update of kind `κ` from `G`, with allowed insertion weights `okW`: an insertion (only
when `κ = incr`) adds a new edge `{u, v}` with `u ≠ v` and an allowed weight; a deletion (only when
`κ = decr`) removes a present edge. -/
def IsLegalUpd {n : ℕ} (okW : Fin n → Fin n → ℕ → Prop) (κ : Kind) (G : WGraph (Fin n)) :
    Upd n → Prop
  | .ins u v c => κ = Kind.incr ∧ u ≠ v ∧ ¬ G.adj.Adj u v ∧ okW u v c
  | .del u v => κ = Kind.decr ∧ G.adj.Adj u v

/-- Every update of the list is legal (of kind `κ`) for the graph it meets, starting from `G`. -/
def IsLegalSeq {n : ℕ} (okW : Fin n → Fin n → ℕ → Prop) (κ : Kind) :
    WGraph (Fin n) → List (Upd n) → Prop
  | _, [] => True
  | G, x :: σ => IsLegalUpd okW κ G x ∧ IsLegalSeq okW κ (x.apply G) σ

/-- An instance of the paper's setting (p. 1 footnote 1, p. 13): the initial graph `G₀` has integer
weights in `[1, W]`, the updates are all insertions (with weights in `[1, W]`) or all deletions,
and every graph `G^(0), …, G^(T)` of the sequence is connected. -/
def IsInstance {n : ℕ} (W : ℕ) (G₀ : WGraph (Fin n)) (κ : Kind) (σ : List (Upd n)) : Prop :=
  G₀.HasWeightsIn W ∧ IsLegalSeq (fun _ _ c => 1 ≤ c ∧ c ≤ W) κ G₀ σ ∧
    ∀ t ≤ σ.length, (graphAt G₀ σ t).adj.Connected

/-- `m`: the number of edges present initially or inserted during the update sequence (p. 1
footnote 1). -/
noncomputable def totalEdges {n : ℕ} (G₀ : WGraph (Fin n)) (σ : List (Upd n)) : ℕ :=
  G₀.adj.edgeSet.ncard + (σ.filter Upd.isIns).length

/-- The graph containing every edge that is ever present: the final graph for insertions, the
initial graph for deletions. -/
def unionGraph {n : ℕ} (G₀ : WGraph (Fin n)) (κ : Kind) (σ : List (Upd n)) : WGraph (Fin n) :=
  match κ with
  | Kind.incr => graphAt G₀ σ σ.length
  | Kind.decr => G₀

/-- Permutations of `Fin n` carry the discrete σ-algebra. -/
instance (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- `log₂ x`, the logarithm used throughout the paper. -/
noncomputable def log2 (x : ℝ) : ℝ := Real.logb 2 x

end PDynTreeEmbed.Main



-- Prove2me | Definitions.Def_OptimalLCA_Matching_Graph
-- name    : OptimalLCA_Matching_Graph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:45:34.24956+00:00
-- url     : https://prove2.me/theorems/6ce2345a-8ca9-458d-9c2e-056a203327fb
-- title:
--   §2.1–2.2 — adjacency-list graphs, ν(G), fractional matchings, ν_f(G), half-integrality, the double cover B(G)
-- statement:
--   A graph on a finite vertex set $V$ is given by **adjacency lists**: for each vertex $w$ an ordered list of its neighbours without repetitions, symmetric ($v$ is listed at $u$ iff $u$ is listed at $v$) and loopless. The order is the fixed but arbitrary order of the neighbour queries: the $i$-th neighbour query at $w$, $1\le i\le\deg(w)$, returns entry $i$ of the list. `MaxDegLE A Δ` says every list has length at most $\Delta$.
--
--   For a finite simple graph $G=(V,E)$:
--   - $\nu(G)$ is the largest size of a matching (a set of edges, each vertex in at most one; the published `MatousekLP.Integrality.IsMatching`).
--   - A **fractional matching** is $f:E\to\mathbb R$ with $f_e\ge 0$ and $\sum_{e\ni v}f_e\le 1$ at every vertex; its value is $\sum_e f_e$, and
--   $$\nu_f(G)=\sup\Big\{\textstyle\sum_e f_e : f \text{ a fractional matching}\Big\},$$
--   a supremum of a nonempty set bounded by $|E|$ (it is attained). $f$ is **half-integral** if every $f_e\in\{0,\tfrac12,1\}$.
--   - The **bipartite double cover** $B(G)$ has vertex set $V\times\{0,1\}$ (the paper's sides $1,2$) and edges $(u,i)(v,j)$ for $uv\in E$, $i\ne j$. Its adjacency lists: the $i$-th neighbour of $(u,j)$ is $(w,1-j)$ where $w$ is the $i$-th neighbour of $u$.
--   - A set $M$ of edges of $B(G)$ induces $x_{uv}=\tfrac12\big(\mathbf 1[(u,0)(v,1)\in M]+\mathbf 1[(v,0)(u,1)\in M]\big)$ on $G$.
--   - $n_0$ is the number of nonisolated vertices.
--
--   **Formalization Note.** Functions on edges are `Sym2 V → ℝ`; only their values on edges of $G$ enter the sums.
-- source:
--   Cohen, Roghani, Optimal LCA and Sublinear Estimation for Bipartite Matching in Δ^O(1/ε) Queries, arXiv:2611.06024 (version not printed; PDF sha256 5a43ec12…3eb3), pp. 2, 11–13, §2.1–§2.2

import Mathlib
import Definitions.Def_MatousekLP_Integrality_BipartiteGraph

/-!
# Graphs, matchings and fractional matchings (Cohen–Roghani, §2.1–§2.2)

Graphs are finite simple graphs. In the query model of §2.1 a graph is given by
adjacency lists: for each vertex `w` an ordered, duplicate-free list of its neighbours
(the "fixed but arbitrary order" of the neighbour queries). The `i`-th neighbour query at
`w` (`1 ≤ i ≤ deg w`) returns entry `i - 1` of the list.

* `matchingNumber G` is `ν(G)`, the largest size of a matching (matchings as in the
  published `MatousekLP.Integrality.IsMatching`);
* `IsFracMatching G f`: `f ≥ 0` on the edges and `∑_{e ∋ v} f e ≤ 1` at every vertex;
  `fracValue G f = ∑_e f e`; `fracMatchingNumber G` is `ν_f(G)`, the supremum of the values
  (the set is nonempty, `f = 0`, and bounded by `|E|`, so this is the largest value);
* `IsHalfIntegral G f`: every edge weight lies in `{0, 1/2, 1}`;
* `doubleCoverGraph G` is the bipartite double cover `B(G)` on `V × Fin 2`
  (the paper's sides `1, 2` are `0, 1`): `(u, i) ~ (v, j)` iff `uv ∈ E` and `i ≠ j`;
* `AdjLists.doubleCover` gives its adjacency lists: the `i`-th neighbour of `(u, j)` is
  `(w, 1 - j)` with `w` the `i`-th neighbour of `u`;
* `projectMatching M` is the weight `x_{uv} = ½(1[(u,1)(v,2) ∈ M] + 1[(v,1)(u,2) ∈ M])`
  induced on `G` by a set `M` of edges of `B(G)` (Lemma 2.3(b));
* `numNonisolated G` is the number `n₀` of vertices of positive degree.
-/

namespace OptimalLCA.Matching

open Finset

/-- Adjacency lists of a finite simple graph on `V`: for each vertex an ordered list of
its neighbours, without repetitions, symmetric and loopless. The list order is the fixed
but arbitrary order of the neighbour queries (§2.1). -/
structure AdjLists (V : Type*) where
  /-- The ordered neighbour list of each vertex. -/
  nbrs : V → List V
  /-- No neighbour is listed twice. -/
  nodup : ∀ u, (nbrs u).Nodup
  /-- `v` is listed at `u` iff `u` is listed at `v`. -/
  symm : ∀ u v, v ∈ nbrs u → u ∈ nbrs v
  /-- No vertex is its own neighbour. -/
  loopless : ∀ u, u ∉ nbrs u

namespace AdjLists

variable {V : Type*}

/-- The simple graph described by adjacency lists. -/
def toGraph (A : AdjLists V) : SimpleGraph V where
  Adj u v := v ∈ A.nbrs u
  symm := ⟨fun u v h => A.symm u v h⟩
  loopless := ⟨fun u h => A.loopless u h⟩

instance instDecidableRelToGraph [DecidableEq V] (A : AdjLists V) :
    DecidableRel A.toGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (v ∈ A.nbrs u))

/-- Every adjacency list has length at most `Δ` (maximum degree at most `Δ`). -/
def MaxDegLE (A : AdjLists V) (Δ : ℕ) : Prop :=
  ∀ u, (A.nbrs u).length ≤ Δ

/-- Adjacency lists of the bipartite double cover: the `i`-th neighbour of `(u, j)` is
`(w, Fin.rev j)` (the paper's `(w, 3 - j)`), where `w` is the `i`-th neighbour of `u`. -/
def doubleCover (A : AdjLists V) : AdjLists (V × Fin 2) where
  nbrs p := (A.nbrs p.1).map (fun w => (w, Fin.rev p.2))
  nodup p := (A.nodup p.1).map (fun a b h => (Prod.mk.inj h).1)
  symm := by
    rintro ⟨u, j⟩ ⟨v, k⟩ h
    simp only [List.mem_map, Prod.mk.injEq] at h ⊢
    obtain ⟨w, hw, rfl, rfl⟩ := h
    exact ⟨u, A.symm _ _ hw, rfl, Fin.rev_rev j⟩
  loopless := by
    rintro ⟨u, j⟩ h
    simp only [List.mem_map, Prod.mk.injEq] at h
    obtain ⟨w, hw, rfl, -⟩ := h
    exact A.loopless _ hw

end AdjLists

section Graphs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `ν(G)`: the largest size of a matching of `G`. -/
noncomputable def matchingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ := by
  classical
  exact (G.edgeFinset.powerset.filter (fun M => MatousekLP.Integrality.IsMatching G M)).sup
    Finset.card

/-- `f : Sym2 V → ℝ` is a fractional matching of `G`: `f e ≥ 0` on every edge and
`∑_{e ∋ v} f e ≤ 1` at every vertex `v` (sums over edges of `G` only). -/
def IsFracMatching (G : SimpleGraph V) [DecidableRel G.Adj] (f : Sym2 V → ℝ) : Prop :=
  (∀ e ∈ G.edgeFinset, 0 ≤ f e) ∧
    ∀ v : V, ∑ e ∈ G.edgeFinset.filter (fun e => v ∈ e), f e ≤ 1

/-- The value `∑_{e ∈ E} f e`. -/
def fracValue (G : SimpleGraph V) [DecidableRel G.Adj] (f : Sym2 V → ℝ) : ℝ :=
  ∑ e ∈ G.edgeFinset, f e

/-- `ν_f(G)`: the largest value of a fractional matching (a supremum of a nonempty set
bounded by `|E|`). -/
noncomputable def fracMatchingNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sSup {r : ℝ | ∃ f : Sym2 V → ℝ, IsFracMatching G f ∧ fracValue G f = r}

/-- Every edge weight lies in `{0, 1/2, 1}`. -/
def IsHalfIntegral (G : SimpleGraph V) [DecidableRel G.Adj] (f : Sym2 V → ℝ) : Prop :=
  ∀ e ∈ G.edgeFinset, f e = 0 ∨ f e = 1 / 2 ∨ f e = 1

/-- The bipartite double cover `B(G)` on `V × Fin 2`. -/
def doubleCoverGraph (G : SimpleGraph V) : SimpleGraph (V × Fin 2) where
  Adj p q := G.Adj p.1 q.1 ∧ p.2 ≠ q.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

instance instDecidableRelDoubleCover (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidableRel (doubleCoverGraph G).Adj :=
  fun p q => inferInstanceAs (Decidable (G.Adj p.1 q.1 ∧ p.2 ≠ q.2))

/-- The weight induced on `G` by a set `M` of edges of `B(G)`:
`x_{uv} = ½ (1[(u,1)(v,2) ∈ M] + 1[(v,1)(u,2) ∈ M])` (sides `1, 2` are `0, 1`). -/
noncomputable def projectMatching (M : Finset (Sym2 (V × Fin 2))) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v =>
    (1 / 2 : ℝ) * ((if s((u, 0), (v, 1)) ∈ M then 1 else 0) +
      (if s((v, 0), (u, 1)) ∈ M then 1 else 0)),
    fun u v => by ring⟩

/-- `n₀`: the number of nonisolated vertices. -/
noncomputable def numNonisolated (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.filter (fun v => 0 < G.degree v)).card

end Graphs

end OptimalLCA.Matching



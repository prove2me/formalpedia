-- Prove2me | Definitions.Def_STCSublinear1377_Main_Weighted
-- name    : STCSublinear1377_Main_Weighted
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:36:38.817287+00:00
-- url     : https://prove2.me/theorems/81f63d06-2e75-4b0b-bb6f-9711fadac22e
-- title:
--   Auxiliary weighted graphs, cuts and hereditary bisection
-- statement:
--   An auxiliary finite undirected graph $F$ has named vertices, edge support and nonnegative weights. Keeping support separate from weights allows zero-capacity edges in the quota problem. The positive-weight and positive-integer-weight regimes are separate predicates. For disjoint sets $A,B$ put
--
--   $$\omega_F(A,B)=\sum_{u\in A,v\in B}\omega_F(uv),\qquad
--   b_F(A)=\omega_F(A,V_F\setminus A),\qquad d_F(v)=b_F(\{v\}).$$
--
--   Weighted route loads sum demand weights, again counting endpoints. A balanced cut has both sides of cardinality at most $2|V_F|/3$. Hereditary bisection is the maximum, over every edge-and-vertex subgraph with at least two vertices, of its minimum balanced-cut weight. It is zero on a singleton. These definitions retain edge deletions, rather than silently replacing all subgraphs by induced subgraphs.
--
--   **Formalization Note** Minima range over explicit finite sets of cuts. The hereditary maximum is the supremum of a finite set of inherited-subgraph values with zero adjoined. The graph data are not restricted to integral weights; Lemma 3.3 uses arbitrary positive real weights.
-- source:
--   Sunny Atalig, Marek Chrobak, Petr Kolman, Hans Raj Tiwary, Sublinear Approximations for Spanning Tree Congestion, STOC 2027 submission #1377 (October 2026), pinned submission, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1377.pdf, §1 preliminaries and hereditary bisection, PDF/printed pp.2–3; §3.3 p.11; Lemma 3.3 p.9

import Definitions.Def_STCSublinear1377_Main_Graph
set_option autoImplicit false

namespace STCSublinear1377.Main

/-- A finite named graph. The support is separate from capacities so a zero-capacity edge need
not disconnect the underlying graph (Proposition 3.6). -/
structure WeightedGraph (n : ℕ) where
  vertices : Finset (Fin n)
  edges : Table n
  weight : Fin n → Fin n → ℝ

def WeightedGraph.wellFormed {n : ℕ} (f : WeightedGraph n) : Prop :=
  (∀ u, f.edges u u = false) ∧ (∀ u v, f.edges u v = f.edges v u) ∧
  (∀ u v, f.weight u v = f.weight v u) ∧
  (∀ u v, 0 ≤ f.weight u v) ∧
  (∀ u v, f.edges u v = true → u ∈ f.vertices ∧ v ∈ f.vertices) ∧
  (∀ u v, f.edges u v = false → f.weight u v = 0)

def WeightedGraph.positive {n : ℕ} (f : WeightedGraph n) : Prop :=
  f.wellFormed ∧ ∀ u v, f.edges u v = true → 0 < f.weight u v

def WeightedGraph.integral {n : ℕ} (f : WeightedGraph n) : Prop :=
  ∀ u v, ∃ w : ℕ, f.weight u v = (w : ℝ)

def WeightedGraph.connected {n : ℕ} (f : WeightedGraph n) : Prop :=
  ((tableGraph f.edges).induce (↑f.vertices : Set (Fin n))).Connected

noncomputable def WeightedGraph.totalWeight {n : ℕ} (f : WeightedGraph n) : ℝ := by
  classical
  exact ∑ u : Fin n, ∑ v : Fin n,
    if u < v ∧ f.edges u v = true then f.weight u v else 0

noncomputable def WeightedGraph.between {n : ℕ} (f : WeightedGraph n)
    (a b : Finset (Fin n)) : ℝ :=
  ∑ u ∈ a, ∑ v ∈ b, f.weight u v

noncomputable def WeightedGraph.boundary {n : ℕ} (f : WeightedGraph n)
    (a : Finset (Fin n)) : ℝ := f.between a (f.vertices \ a)

noncomputable def WeightedGraph.degree {n : ℕ} (f : WeightedGraph n) (v : Fin n) : ℝ :=
  f.boundary {v}

def WeightedGraph.connectedSet {n : ℕ} (f : WeightedGraph n)
    (a : Finset (Fin n)) : Prop :=
  a ⊆ f.vertices ∧ a.Nonempty ∧ ((tableGraph f.edges).induce (↑a : Set (Fin n))).Connected

def WeightedGraph.tree {n : ℕ} (f : WeightedGraph n) (t : Table n) : Prop :=
  (∀ u, t u u = false) ∧ (∀ u v, t u v = t v u) ∧
  tableGraph t ≤ tableGraph f.edges ∧
  ((tableGraph t).induce (↑f.vertices : Set (Fin n))).IsTree

noncomputable def WeightedGraph.edgeLoad {n : ℕ} (f : WeightedGraph n)
    (t : Table n) (x y : Fin n) : ℝ := by
  classical
  exact ∑ u : Fin n, ∑ v : Fin n,
    if u < v ∧ f.edges u v = true ∧ usesEdge t u v x y then f.weight u v else 0

noncomputable def WeightedGraph.vertexLoad {n : ℕ} (f : WeightedGraph n)
    (t : Table n) (z : Fin n) : ℝ := by
  classical
  exact ∑ u : Fin n, ∑ v : Fin n,
    if u < v ∧ f.edges u v = true ∧ visitsVertex t u v z then f.weight u v else 0

/-- Finite nonnegative maximum, explicitly zero when there is no tree edge. -/
noncomputable def WeightedGraph.congestion {n : ℕ} (f : WeightedGraph n)
    (t : Table n) : ℝ := by
  classical
  exact (Finset.univ : Finset (Fin n × Fin n)).fold max 0
    (fun e => if t e.1 e.2 = true then f.edgeLoad t e.1 e.2 else 0)

noncomputable def WeightedGraph.induced {n : ℕ} (f : WeightedGraph n)
    (a : Finset (Fin n)) : WeightedGraph n := by
  classical
  exact ⟨f.vertices ∩ a,
    fun u v => f.edges u v && decide (u ∈ a ∧ v ∈ a),
    fun u v => if u ∈ a ∧ v ∈ a then f.weight u v else 0⟩

/-- A genuine edge-and-vertex subgraph, not just an induced graph. -/
def WeightedGraph.subgraph {n : ℕ} (j f : WeightedGraph n) : Prop :=
  j.wellFormed ∧ j.vertices ⊆ f.vertices ∧
  (∀ u v, j.edges u v = true → f.edges u v = true ∧ j.weight u v = f.weight u v)

noncomputable def WeightedGraph.mincut {n : ℕ} (f : WeightedGraph n)
    (a b : Finset (Fin n)) : ℝ := by
  classical
  let costs := (f.vertices.powerset.filter (fun x => a ⊆ x ∧ Disjoint x b)).image f.boundary
  exact if h : costs.Nonempty then costs.min' h else 0

noncomputable def WeightedGraph.bisection {n : ℕ} (f : WeightedGraph n) : ℝ := by
  classical
  let costs := (f.vertices.powerset.filter (fun x =>
    3 * x.card ≤ 2 * f.vertices.card ∧
      3 * (f.vertices \ x).card ≤ 2 * f.vertices.card)).image f.boundary
  exact if h : costs.Nonempty then costs.min' h else 0

/-- The maximum ranges over every subgraph with at least two vertices. Finite support and fixed
inherited edge weights make the set of bisection values finite. Singleton/empty convention: zero. -/
noncomputable def WeightedGraph.hereditaryBisection {n : ℕ} (f : WeightedGraph n) : ℝ :=
  sSup (insert 0 {b | ∃ j : WeightedGraph n, j.subgraph f ∧ 2 ≤ j.vertices.card ∧ j.bisection = b})

noncomputable def original {n : ℕ} (g : Table n) : WeightedGraph n := by
  classical
  exact ⟨Finset.univ, fun u v => decide ((tableGraph g).Adj u v),
    fun u v => if (tableGraph g).Adj u v then 1 else 0⟩

end STCSublinear1377.Main



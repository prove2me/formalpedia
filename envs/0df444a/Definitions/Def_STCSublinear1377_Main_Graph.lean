-- Prove2me | Definitions.Def_STCSublinear1377_Main_Graph
-- name    : STCSublinear1377_Main_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:35:55.061252+00:00
-- url     : https://prove2.me/theorems/3c27f7aa-c91d-4d06-8db5-6816eae7bd3b
-- title:
--   Graphs, endpoint-inclusive loads and spanning tree congestion
-- statement:
--   For a finite simple graph $G$ on $n$ named vertices, a spanning tree $T$ is a connected acyclic spanning subgraph. Every undirected edge $uv$ of $G$ supplies one demand routed on its unique simple path $P_T(u,v)$ in $T$. Define
--
--   $$c_{G,T}(xy)=\#\{uv\in E(G):xy\in E(P_T(u,v))\},\qquad
--   \ell_{G,T}(z)=\#\{uv\in E(G):z\in V(P_T(u,v))\}.$$
--
--   The tree edge's own demand contributes to its edge load, and both endpoints contribute to vertex load. The congestion $c(G,T)$ is the maximum edge load, with value zero for a tree on one vertex. The optimum $k=\operatorname{STC}(G)$ is the minimum over the finite set of spanning trees, rather than an input parameter. These objects provide the objective shared by the goal and baseline.
--
--   **Formalization Note** The graph is a Boolean adjacency table on `Fin n`. The input predicate enforces symmetry, a false diagonal and connectivity. Each undirected demand is counted once using the order on names. The minimum is a finite attained minimum when trees exist and is explicitly zero otherwise. This latter convention is never used for a connected input of order at least two.
-- source:
--   Sunny Atalig, Marek Chrobak, Petr Kolman, Hans Raj Tiwary, Sublinear Approximations for Spanning Tree Congestion, STOC 2027 submission #1377 (October 2026), pinned submission, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1377.pdf, §1 preliminaries, PDF/printed pp.2–3, definition of loads and (1.1)

import Mathlib
set_option autoImplicit false

namespace STCSublinear1377.Main

/-- A binary adjacency table; symmetry and absence of loops are checked separately. -/
abbrev Table (n : ℕ) := Fin n → Fin n → Bool

def tableGraph {n : ℕ} (a : Table n) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ a u v = true ∧ a v u = true
  symm := ⟨by intro u v h; exact ⟨Ne.symm h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

def isInput {n : ℕ} (a : Table n) : Prop :=
  (∀ u, a u u = false) ∧ (∀ u v, a u v = a v u) ∧ (tableGraph a).Connected

def spanning {n : ℕ} (g t : Table n) : Prop :=
  (∀ u, t u u = false) ∧ (∀ u v, t u v = t v u) ∧
    tableGraph t ≤ tableGraph g ∧ (tableGraph t).IsTree

/-- The endpoint-inclusive route convention from p.2, expressed without selecting a path. -/
def visitsVertex {n : ℕ} (t : Table n) (u v z : Fin n) : Prop :=
  ∃ p : (tableGraph t).Walk u v, p.IsPath ∧ z ∈ p.support

def usesEdge {n : ℕ} (t : Table n) (u v x y : Fin n) : Prop :=
  ∃ p : (tableGraph t).Walk u v, p.IsPath ∧ s(x, y) ∈ p.edges

noncomputable def edgeLoad {n : ℕ} (g t : Table n) (x y : Fin n) : ℕ := by
  classical
  exact ∑ u : Fin n, ∑ v : Fin n,
    if u < v ∧ (tableGraph g).Adj u v ∧ usesEdge t u v x y then 1 else 0

noncomputable def vertexLoad {n : ℕ} (g t : Table n) (z : Fin n) : ℕ := by
  classical
  exact ∑ u : Fin n, ∑ v : Fin n,
    if u < v ∧ (tableGraph g).Adj u v ∧ visitsVertex t u v z then 1 else 0

noncomputable def congestion {n : ℕ} (g t : Table n) : ℕ := by
  classical
  exact (Finset.univ : Finset (Fin n × Fin n)).sup
    (fun e => if (tableGraph t).Adj e.1 e.2 then edgeLoad g t e.1 e.2 else 0)

noncomputable def edgeCount {n : ℕ} (g : Table n) : ℕ := by
  classical
  exact ∑ u : Fin n, ∑ v : Fin n, if u < v ∧ (tableGraph g).Adj u v then 1 else 0

/-- An attained finite minimum whenever a spanning tree exists; zero otherwise. -/
noncomputable def stc {n : ℕ} (g : Table n) : ℕ := by
  classical
  let values := ((Finset.univ : Finset (Table n)).filter (spanning g)).image (congestion g)
  exact if h : values.Nonempty then values.min' h else 0

end STCSublinear1377.Main



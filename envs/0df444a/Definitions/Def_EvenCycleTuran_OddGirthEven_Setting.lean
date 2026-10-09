-- Prove2me | Definitions.Def_EvenCycleTuran_OddGirthEven_Setting
-- name    : EvenCycleTuran_OddGirthEven_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:27.849558+00:00
-- url     : https://prove2.me/theorems/01231122-3489-4e1c-9bf8-bdc31e282bd2
-- title:
--   Finite graphs, forbidden cycle families, hypergraph girth, and distance layers
-- statement:
--   For a finite simple graph $G$, a set $A$ of cycle lengths, and a graph $H$, write $G$ as $\mathcal C_A$-free when it has no subgraph isomorphic to $C_a$ for any $a\in A$. The generalized Turán number is
--
--   $$\operatorname{ex}(n,H,\mathcal C_A)=\max\{\mathcal N(H,G): |V(G)|=n,\ G\text{ is }\mathcal C_A\text{-free}\},$$
--
--   where $\mathcal N(H,G)$ counts unlabelled copies. The layer $N_i(v)$ consists of vertices at distance exactly $i$ from $v$, excluding unreachable vertices. A hypergraph is a finite set of distinct vertex sets; it is $r$-uniform when every edge has $r$ vertices. Its Berge girth is at least $s$ when it has no Berge cycle of any length $2,\ldots,s-1$. A Berge cycle alternates distinct vertices and distinct hyperedges, with each edge containing its consecutive vertices.
--
--   These definitions support both bounds of Theorem 17 and its local counting lemmas. The edge-replacement graph uses a cyclic ordering of each hyperedge; cycle counts through a vertex and edge counts within or between layers count each unlabelled object once.
--
--   **Formalization Note** Graphs in the extremal number have vertex type $\operatorname{Fin}(n)$. An empty hypergraph has girth at least every threshold. Extended graph distance keeps unreachable vertices outside $N_0(v)$.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, pp. 2–3 (§1, §1.1), p. 27 (§6.2)

import Mathlib
import Definitions.Def_EvenCycleTuran_C4Count_Setting

namespace EvenCycleTuran.OddGirthEven

/-- Vertices at extended graph distance exactly `i` from `v`. -/
def layer {V : Type*} (G : SimpleGraph V) (v : V) (i : ℕ) : Set V :=
  {w | G.edist v w = i}

/-- A finite simple hypergraph is represented by its set of distinct hyperedges. -/
abbrev Hypergraph (V : Type*) := Finset (Finset V)

/-- Every hyperedge has exactly `r` vertices. -/
def IsUniform {V : Type*} (H : Hypergraph V) (r : ℕ) : Prop :=
  ∀ e ∈ H, e.card = r

/-- A Berge cycle has distinct vertices and distinct hyperedges, in alternating order. -/
def nextIdx (j : ℕ) (hj : 0 < j) (i : Fin j) : Fin j :=
  ⟨(i.val + 1) % j, Nat.mod_lt _ hj⟩

/-- Existence of a Berge cycle of length `j`. -/
def HasBergeCycle {V : Type*} (H : Hypergraph V) (j : ℕ) : Prop :=
  ∃ (hj : 0 < j) (v : Fin j ↪ V) (h : Fin j ↪ Finset V),
    ∀ i : Fin j, h i ∈ H ∧ v i ∈ h i ∧ v (nextIdx j hj i) ∈ h i

/-- Hypergraph girth at least `s`: no Berge cycle of any length from 2 to `s-1`. -/
def GirthGe {V : Type*} (H : Hypergraph V) (s : ℕ) : Prop :=
  ∀ j, 2 ≤ j → j < s → ¬ HasBergeCycle H j

/-- Replace every `r`-vertex hyperedge with a cycle in the order supplied by `σ`. -/
def replaceEdges {V : Type*} (H : Hypergraph V) (r : ℕ)
    (σ : (e : {e // e ∈ H}) → Fin r ↪ V) : SimpleGraph V :=
  ⨆ e : {e // e ∈ H}, (SimpleGraph.cycleGraph r).map (σ e)

/-- The number of unlabelled `C_{2l+1}` copies containing `v`. -/
noncomputable def cyclesAt {V : Type*} [Fintype V] (G : SimpleGraph V) (l : ℕ) (v : V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun S : G.Subgraph =>
    Nonempty (SimpleGraph.cycleGraph (2 * l + 1) ≃g S.coe) ∧ v ∈ S.verts)).card

/-- Number of edges whose endpoints both lie in `S`. -/
noncomputable def edgesInside {V : Type*} [Fintype V]
    (G : SimpleGraph V) (S : Set V) : ℕ := by
  classical
  exact (G.edgeFinset.filter (fun e => ∃ u v, e = s(u, v) ∧ u ∈ S ∧ v ∈ S)).card

/-- Number of edges with one endpoint in each of two vertex sets. -/
noncomputable def edgesBetween {V : Type*} [Fintype V]
    (G : SimpleGraph V) (S T : Set V) : ℕ := by
  classical
  exact (G.edgeFinset.filter (fun e => ∃ u v, e = s(u, v) ∧ u ∈ S ∧ v ∈ T)).card

end EvenCycleTuran.OddGirthEven



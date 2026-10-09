-- Prove2me | Definitions.Def_EvenCycleTuran_OddGirthOdd_Setting
-- name    : EvenCycleTuran_OddGirthOdd_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T19:24:23.600992+00:00
-- url     : https://prove2.me/theorems/08a57a3f-4164-4cc0-82ac-156a65d67e5c
-- title:
--   pp. 2–3, 27 — 𝒞_A-free graphs, ex(n, H, 𝒞_A), distance layers N_i(v), Berge cycles and hypergraph girth
-- statement:
--   This file fixes the objects of §6.2 of Gerbner, Győri, Methuku and Vizer, *Generalized Turán problems for even cycles*.
--
--   1. **Cycle-free graphs.** For a set $A$ of integers $a \ge 3$, a graph $G$ is $\mathcal C_A$-free if it contains no cycle $C_a$ with $a \in A$ as a (not necessarily induced) subgraph.
--   2. **Generalized Turán number.** For a graph $H$,
--   $$\mathrm{ex}(n, H, \mathcal C_A) = \max\{\mathcal N(H, G) : G \text{ a } \mathcal C_A\text{-free graph on } n \text{ vertices}\},$$
--   where $\mathcal N(H, G)$ is the number of unlabelled copies of $H$ in $G$, i.e. the number of subgraphs of $G$ isomorphic to $H$.
--   3. **Distance layers.** For a vertex $v$, $N_i(v)$ is the set of vertices at distance exactly $i$ from $v$; vertices in other components belong to no layer.
--   4. **Hypergraphs.** A hypergraph is a finite set of distinct hyperedges (finite vertex sets); it is $r$-uniform if every hyperedge has $r$ vertices. A **Berge cycle of length $j$** (Berge-$C_j$) is an alternating sequence $v_1, h_1, v_2, h_2, \dots, v_j, h_j, v_1$ of distinct vertices and distinct hyperedges with $v_i, v_{i+1} \in h_i$ for $i < j$ and $v_j, v_1 \in h_j$. A hypergraph has **girth at least $s$** if it contains no Berge-$C_j$ with $2 \le j < s$.
--   5. **Replacing hyperedges by cycles.** Given an $r$-uniform hypergraph and, for each hyperedge, a cyclic ordering of its $r$ vertices, the graph obtained by replacing each hyperedge by the cycle $C_r$ through its vertices in that order.
--   6. **Local counts.** The number of copies of $C_{2l+1}$ containing a given vertex $v$, and the number of edges of $G$ with both endpoints in a vertex set $S$ ("edges inside $S$").
--
--   These objects are shared by the goal theorem (Theorem 18) and its milestones.
--
--   **Formalization Note** Vertices of an $n$-vertex graph are `Fin n`; copies are counted with Mathlib's `copyCount` (unlabelled), cycles are Mathlib's `cycleGraph`. `exCyc` is an `sSup` of a set of natural numbers that is nonempty (the empty graph is $\mathcal C_A$-free when every $a \in A$ is at least 3) and finite, so it is a true maximum. $N_i(v)$ uses the extended distance `edist`, which is $\infty$ between different components. Girth is encoded as the predicate "girth at least $s$", never as an infimum, so a hypergraph with no Berge cycle has every girth. The Berge-cycle predicate itself is only used for $j \ge 2$, as in the paper.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 2 (notation, N_i(v)), p. 3 (ex(n, H, F), Berge cycles), p. 27 (girth of a hypergraph)

import Mathlib

namespace EvenCycleTuran.OddGirthOdd

/-- `G` contains no cycle of length `a` for any `a ∈ A` (`G` is 𝒞_A-free). -/
def CycleFree {V : Type*} (A : Set ℕ) (G : SimpleGraph V) : Prop :=
  ∀ a ∈ A, (SimpleGraph.cycleGraph a).Free G

/-- ex(n, H, 𝒞_A): the maximum number of unlabelled copies of `H` in an `n`-vertex
𝒞_A-free graph. -/
noncomputable def exCyc {W : Type*} (n : ℕ) (H : SimpleGraph W) (A : Set ℕ) : ℕ :=
  sSup {N | ∃ G : SimpleGraph (Fin n), CycleFree A G ∧ G.copyCount H = N}

/-- `N_i(v)`: the vertices at (extended) graph distance exactly `i` from `v`.
Vertices in other components have `edist = ⊤` and lie in no layer. -/
def layer {V : Type*} (G : SimpleGraph V) (v : V) (i : ℕ) : Set V :=
  {w | G.edist v w = i}

/-- A finite hypergraph, represented by its set of distinct hyperedges. -/
abbrev Hypergraph (V : Type*) := Finset (Finset V)

/-- Every hyperedge has exactly `r` vertices. -/
def IsUniform {V : Type*} (H : Hypergraph V) (r : ℕ) : Prop :=
  ∀ e ∈ H, e.card = r

/-- The cyclic successor `i ↦ i + 1 (mod j)` on `Fin j`. -/
def nextIdx (j : ℕ) (hj : 0 < j) (i : Fin j) : Fin j :=
  ⟨(i.val + 1) % j, Nat.mod_lt _ hj⟩

/-- `H` contains a Berge cycle of length `j`: distinct vertices `v 0, …, v (j-1)` and distinct
hyperedges `h 0, …, h (j-1)` of `H` with `v i, v (i+1 mod j) ∈ h i`. The paper's notion
(Berge-C_j) is for `j ≥ 2`; `GirthGe` only queries `j ≥ 2`. -/
def HasBergeCycle {V : Type*} (H : Hypergraph V) (j : ℕ) : Prop :=
  ∃ (hj : 0 < j) (v : Fin j ↪ V) (h : Fin j ↪ Finset V),
    ∀ i : Fin j, h i ∈ H ∧ v i ∈ h i ∧ v (nextIdx j hj i) ∈ h i

/-- `H` has girth at least `s`: no Berge cycle of any length `j` with `2 ≤ j < s`. -/
def GirthGe {V : Type*} (H : Hypergraph V) (s : ℕ) : Prop :=
  ∀ j, 2 ≤ j → j < s → ¬ HasBergeCycle H j

/-- Replace every hyperedge `e` of an `r`-uniform hypergraph by a copy of `C_r`, traversing
its vertices in the cyclic order `σ e`. -/
def replaceEdges {V : Type*} (H : Hypergraph V) (r : ℕ)
    (σ : (e : {e // e ∈ H}) → Fin r ↪ V) : SimpleGraph V :=
  ⨆ e : {e // e ∈ H}, (SimpleGraph.cycleGraph r).map (σ e)

/-- The number of unlabelled copies of `C_{2l+1}` in `G` that contain the vertex `v`. -/
noncomputable def cyclesAt {V : Type*} [Fintype V] (G : SimpleGraph V) (l : ℕ) (v : V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun S : G.Subgraph =>
    Nonempty (SimpleGraph.cycleGraph (2 * l + 1) ≃g S.coe) ∧ v ∈ S.verts)).card

/-- The number of edges of `G` with both endpoints in `S`. -/
noncomputable def edgesInside {V : Type*} [Fintype V]
    (G : SimpleGraph V) (S : Set V) : ℕ := by
  classical
  exact (G.edgeFinset.filter (fun e => ∃ u v, e = s(u, v) ∧ u ∈ S ∧ v ∈ S)).card

end EvenCycleTuran.OddGirthOdd



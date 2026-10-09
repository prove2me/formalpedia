-- Prove2me | Definitions.Def_EvenCycleTuran_C4Count_Setting
-- name    : EvenCycleTuran_C4Count_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T20:22:30.936619+00:00
-- url     : https://prove2.me/theorems/8e74b32f-f4dc-464e-a77f-9fa4d5198c78
-- title:
--   pp. 2–3, 12 — 𝒞_A-free graphs, ex(n, H, 𝒞_A), K_{a,n−a}, fat pairs, fat C₄'s and the greedy multiplicity m(e)
-- statement:
--   All graphs are finite simple graphs. For a graph $G$ and a set $A$ of integers, $G$ is **$\mathcal C_A$-free** if it contains no cycle $C_a$ with $a\in A$ as a (not necessarily induced) subgraph. For a graph $H$, the **generalized Turán number**
--
--   $$\mathrm{ex}(n,H,\mathcal C_A)=\max\{\mathcal N(H,G) : G \text{ is a } \mathcal C_A\text{-free graph on } n \text{ vertices}\}$$
--
--   is the largest number of copies of $H$ in such a graph, where $\mathcal N(H,G)$ is the number of (unlabelled) copies of $H$ in $G$, i.e. the number of subgraphs of $G$ isomorphic to $H$. With $A=\{2k\}$ this is $\mathrm{ex}(n,H,C_{2k})$.
--
--   The file also fixes the objects of the proof of Theorem 11 (§4.1):
--
--   1. $K_{a,n-a}$, the complete bipartite graph on the vertex set $\{0,\dots,n-1\}$ whose classes are $\{v<a\}$ and $\{v\ge a\}$.
--   2. The **codegree** $f(a,b)=|N(a)\cap N(b)|$ of two vertices and the **common neighbourhood** $\bigcap_{s\in S}N(s)$ of a vertex set $S$.
--   3. A **fat pair**: two distinct vertices with at least $k$ common neighbours.
--   4. A **copy of $C_4$**: a subgraph of $G$ isomorphic to $C_4$. It is **fat** if both of its pairs of opposite (distinct, non-adjacent) vertices are fat pairs, and **non-fat** otherwise.
--   5. A **greedy run**: the fat $C_4$'s of $G$ listed once each, in an arbitrary order, and for the $j$-th one an edge picked from its four edges, always one that was picked the smallest number of times before. The **multiplicity** $m(e)$ of an edge $e$ is the number of times it is picked.
--
--   These are the objects in terms of which Theorem 11 and the steps of its proof are stated.
--
--   **Formalization Note** Vertices are `Fin n`; $C_a$ is Mathlib's `cycleGraph a` and $\mathcal N(H,G)$ is `G.copyCount H`. `exCyc` is an `sSup` of a set of naturals; when every length in $A$ is at least 3 the set is nonempty (the empty graph qualifies) and finite, so the value is a true maximum (checked in the sanity file). A greedy run is a structure: the list of fat $C_4$'s (without repetition), the picked edge of each, and the greedy rule "the picked edge was picked before no more often than any other edge of that $C_4$".
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 2 (𝒩(H,G), 𝒞_A), p. 3 (ex(n,H,𝓕)), p. 12 (§4.1: fat pairs, fat C4's, multiplicity m(e))

import Mathlib

namespace EvenCycleTuran.C4Count
open Finset SimpleGraph

/-- `G` contains no cycle of length `a` for any `a ∈ A` (`G` is 𝒞_A-free). -/
def CycleFree {V : Type*} (A : Set ℕ) (G : SimpleGraph V) : Prop :=
  ∀ a ∈ A, (cycleGraph a).Free G

/-- ex(n, H, 𝒞_A): the maximum number of copies of `H` in an `n`-vertex 𝒞_A-free graph. -/
noncomputable def exCyc {W : Type*} (n : ℕ) (H : SimpleGraph W) (A : Set ℕ) : ℕ :=
  sSup {N | ∃ G : SimpleGraph (Fin n), CycleFree A G ∧ G.copyCount H = N}

/-- K_{a, n−a} on `Fin n`: the vertices `< a` form one class, the rest the other. -/
def bipGraph (n a : ℕ) : SimpleGraph (Fin n) where
  Adj v w := ((v : ℕ) < a ↔ ¬ (w : ℕ) < a)
  symm := ⟨fun _ _ h => by tauto⟩
  loopless := ⟨fun _ h => by tauto⟩

instance (n a : ℕ) : DecidableRel (bipGraph n a).Adj := fun v w =>
  show Decidable (((v : ℕ) < a ↔ ¬ (w : ℕ) < a)) from inferInstance

/-- f(a, b): the number of common neighbours of `a` and `b`. -/
def codeg {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : V) : ℕ :=
  #(G.neighborFinset a ∩ G.neighborFinset b)

/-- The common neighbourhood of a set `S` of vertices: the vertices adjacent to every vertex
of `S`. -/
def commonNbrs {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : Finset V :=
  {w | ∀ s ∈ S, G.Adj s w}

/-- A fat pair (p. 12): two distinct vertices with at least `k` common neighbours. -/
def IsFatPair {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (a b : V) : Prop :=
  a ≠ b ∧ k ≤ codeg G a b

/-- A copy of C₄ in `G`: a subgraph of `G` isomorphic to `cycleGraph 4` (the objects counted
by `G.copyCount (cycleGraph 4)`). -/
def IsC4 {V : Type*} {G : SimpleGraph V} (G' : G.Subgraph) : Prop :=
  Nonempty (cycleGraph 4 ≃g G'.coe)

/-- A fat C₄ (p. 12): a copy of C₄ both of whose pairs of opposite vertices (the pairs of
distinct, non-adjacent vertices of the copy) are fat. -/
def IsFatC4 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (G' : G.Subgraph) : Prop :=
  IsC4 G' ∧ ∀ a ∈ G'.verts, ∀ b ∈ G'.verts, a ≠ b → ¬ G'.Adj a b → IsFatPair G k a b

/-- The number of fat C₄'s of `G`. -/
noncomputable def fatC4Count {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) : ℕ := by
  classical exact #{G' : G.Subgraph | IsFatC4 G k G'}

/-- The number of non-fat C₄'s of `G` (copies of C₄ that are not fat). -/
noncomputable def nonFatC4Count {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) : ℕ := by
  classical exact #{G' : G.Subgraph | IsC4 G' ∧ ¬ IsFatC4 G k G'}

/-- A run of the greedy edge-picking procedure of p. 12: the fat C₄'s of `G` listed in an
arbitrary order (each exactly once), and for the `j`-th one an edge `pick j` of it, chosen
among its four edges as one that was picked the smallest number of times before. -/
structure GreedyRun {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) where
  /-- the fat C₄'s in the order they are processed -/
  L : List G.Subgraph
  nodup : L.Nodup
  mem_iff : ∀ G' : G.Subgraph, G' ∈ L ↔ IsFatC4 G k G'
  /-- the edge picked from the `j`-th fat C₄ -/
  pick : Fin L.length → Sym2 V
  pick_mem : ∀ j, pick j ∈ (L.get j).edgeSet
  greedy : ∀ j, ∀ e ∈ (L.get j).edgeSet,
    #{i : Fin L.length | i < j ∧ pick i = pick j} ≤ #{i : Fin L.length | i < j ∧ pick i = e}

/-- m(e), the multiplicity of `e` (p. 12): the number of times `e` is picked in the run. -/
def GreedyRun.mult {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {k : ℕ} (R : GreedyRun G k) (e : Sym2 V) : ℕ :=
  #{j : Fin R.L.length | R.pick j = e}

end EvenCycleTuran.C4Count



-- Prove2me | Definitions.Def_TenChallenges_Hypergraph
-- name    : TenChallenges_Hypergraph
-- status  : Definition
-- author  : @utkuokur
-- created : 2026-11-04T21:15:20.441794+00:00
-- url     : https://prove2.me/theorems/4402a9e9-a968-4ae2-a1dd-4b41229c9b3c
-- title:
--   Finite hypergraphs: uniformity, partiteness, cover number, matching number, and Ryser's inequality
-- statement:
--   The definitions behind Challenge 8 of the Ten Challenges benchmark.
--
--   1. **Finite hypergraph.** A structure with a finite set of *vertices* and a set of *edges*, each edge a finite subset of the vertices.
--   2. **Uniform, partite.** $\mathcal H$ is *$r$-uniform* if every edge has exactly $r$ elements; it is *$r$-partite* if there are parts $P_0,\dots,P_{r-1}$, pairwise disjoint, whose union is the vertex set, such that every edge meets every part in exactly one vertex.
--   3. **Covers and matchings.** A *vertex cover* is a subset $C$ of the vertices meeting every edge; a *matching* is a finite set of edges that are pairwise disjoint.
--   4. **Cover and matching numbers.** $\tau(\mathcal H)$ is the least cardinality of a vertex cover and $\nu(\mathcal H)$ the largest cardinality of a matching, as natural numbers.
--   5. **Ryser's inequality at $r$.** $\mathrm{RyserConjectureFor}(\mathcal H,r)$ says: if $\mathcal H$ is $r$-uniform and $r$-partite then
--   $$\tau(\mathcal H)\le (r-1)\cdot\nu(\mathcal H).$$
--
--   **Formalization Note.** $\tau$ is `sInf` of the set of sizes of covers and $\nu$ is `sSup` of the set of sizes of matchings in $\mathbb N$, with $\inf\emptyset = 0$ and $\sup$ of an unbounded set $=0$ by convention; edges form a `Set (Finset α)`, necessarily finite. The vertex type carries decidable equality.
-- source:
--   Ten Challenges repository, file Defs_and_Lems/Hypergraph.lean (commit ff14a56), https://github.com/TenChallenges/ten-challenges/blob/main/Defs_and_Lems/Hypergraph.lean; conjecture as in R. Aharoni, Ryser's conjecture for tripartite 3-graphs, Combinatorica 21 (2001), introduction.

import Mathlib.Order.Lattice.Nat

/-- A finite hypergraph with edges contained in its vertex set. -/
structure FinHypergraph (α : Type*) where
  vertices : Finset α
  edges : Set (Finset α)
  edges_subset_vertices : ∀ e ∈ edges, e ⊆ vertices

variable {V : Type*} [DecidableEq V] (H : FinHypergraph V)

namespace FinHypergraph

/-- An `r`-uniform hypergraph has every edge of cardinality `r`. -/
def IsUniform (r : ℕ) : Prop :=
  ∀ e ∈ H.edges, e.card = r

/-- An `r`-partite hypergraph has its vertices partitioned into `r` parts, and
every edge meets every part in exactly one vertex. -/
def IsPartite (r : ℕ) : Prop :=
  ∃ parts : Fin r → Finset V,
    (∀ v : V, v ∈ H.vertices ↔ ∃ i : Fin r, v ∈ parts i) ∧
      (∀ i j : Fin r, i ≠ j → Disjoint (parts i) (parts j)) ∧
        (∀ e ∈ H.edges, ∀ i : Fin r, (parts i ∩ e).card = 1)

/-- A vertex cover is a set of vertices meeting every edge. -/
def IsVertexCover (C : Finset V) : Prop :=
  C ⊆ H.vertices ∧ ∀ e ∈ H.edges, ∃ v ∈ C, v ∈ e

/-- A matching is a finite set of pairwise disjoint edges. -/
def IsMatching (M : Finset (Finset V)) : Prop :=
  (∀ e ∈ M, e ∈ H.edges) ∧
    ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → Disjoint e₁ e₂

/-- The cover number `τ(H)`: the least cardinality of a vertex cover, as an
`sInf` over the achievable cover cardinalities (`0` if no cover exists). -/
noncomputable def coverNumber : ℕ :=
  sInf {n | ∃ C : Finset V, H.IsVertexCover C ∧ C.card = n}

/-- The matching number `ν(H)`: the largest size of a matching, as an `sSup`
over the achievable matching sizes. -/
noncomputable def matchingNumber : ℕ :=
  sSup {n | ∃ M : Finset (Finset V), H.IsMatching M ∧ M.card = n}

/-- Ryser's hypergraph conjecture for a fixed value of `r`. -/
def RyserConjectureFor (r : ℕ) : Prop :=
  H.IsUniform r → H.IsPartite r → H.coverNumber ≤ (r - 1) * H.matchingNumber

end FinHypergraph



-- Prove2me | Definitions.Def_TenChallenges_Minor
-- name    : TenChallenges_Minor
-- status  : Definition
-- author  : @utkuokur
-- created : 2026-11-04T21:24:57.041216+00:00
-- url     : https://prove2.me/theorems/1037f58c-7618-403f-ba39-e4c1f5f21521
-- title:
--   Graph minors, the Hadwiger number and Wagner planarity
-- statement:
--   The minor relation for Mathlib's simple graphs, shared by Challenges 1 and 6 of the Ten Challenges benchmark.
--
--   1. **Minor.** For graphs $H$ on $W$ and $G$ on $V$, a *minor structure* of $H$ in $G$ consists of **branch sets** $B_w\subseteq V$ for $w\in W$ which are pairwise disjoint, each inducing a connected (hence nonempty) subgraph of $G$, such that for every edge $w_1w_2$ of $H$ some vertex of $B_{w_1}$ is adjacent in $G$ to some vertex of $B_{w_2}$. $H$ is a minor of $G$ when such a structure exists.
--   2. **Hadwiger number.** For a finite graph $G$, $h(G)$ is the largest $r\le |V|$ such that the complete graph $K_r$ is a minor of $G$.
--   3. **Planarity.** $K_5$ and $K_{3,3}$ denote the complete graph on five vertices and the complete bipartite graph with sides of size three; $G$ is *Wagner-planar* if neither $K_5$ nor $K_{3,3}$ is a minor of $G$. By Wagner's theorem this is planarity for finite graphs.
--
--   **Formalization Note.** `Minor H G` is a structure (data, not a proposition); "$H$ is a minor of $G$" is `Nonempty (Minor H G)`. The Hadwiger number is `Nat.findGreatest` over $r\le|V|$, so it is $0$ for the graph with no vertices.
-- source:
--   Ten Challenges repository, file Defs_and_Lems/Minor.lean (commit ff14a56), https://github.com/TenChallenges/ten-challenges/blob/main/Defs_and_Lems/Minor.lean; definitions following R. Diestel, Graph Theory, 5th ed., Sections 1.7 and 4.4.

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

namespace SimpleGraph

variable {V W : Type*}

/-- The data witnessing that `H` is a minor of `G`, as simple graphs. -/
structure Minor (H : SimpleGraph W) (G : SimpleGraph V) where
  /-- The branch sets of the minor.

  Seeing the minor as a quotient graph, `branchSet w` is exactly the fiber of `w` under the quotient
  map. -/
  branchSet : W → Set V
  /-- The branch sets are pairwise disjoint. -/
  pairwise_disjoint_branchSet : Pairwise fun w₁ w₂ ↦ Disjoint (branchSet w₁) (branchSet w₂)
  /-- Each branch set is connected (in particular nonempty). -/
  connectedOn_branchSet (w : W) : (G.induce (branchSet w)).Connected
  /-- Adjacency in the minor induce adjacency between some points of the corresponding branch set.
  -/
  exists_mem_branchSet_of_adj ⦃w₁ w₂ : W⦄ :
    H.Adj w₁ w₂ → ∃ v₁ ∈ branchSet w₁, ∃ v₂ ∈ branchSet w₂, G.Adj v₁ v₂

/-- The Hadwiger number: the largest `r` such that `K_r` is a minor of `G`. -/
noncomputable def hadwigerNumber [Fintype V] (G : SimpleGraph V) : ℕ := by
  classical
  exact Nat.findGreatest (fun r =>
    Nonempty (Minor (completeGraph (Fin r)) G)) (Fintype.card V)

/-- K₅ -/
abbrev K5 := completeGraph (Fin 5)

/-- K₃,₃ -/
abbrev K33 := completeBipartiteGraph (Fin 3) (Fin 3)

/-- Planarity via Wagner's criterion: no `K₅` or `K₃,₃` minor. -/
def IsWagnerPlanar (G : SimpleGraph V) : Prop :=
  ¬ Nonempty (Minor K5 G) ∧ ¬ Nonempty (Minor K33 G)

end SimpleGraph



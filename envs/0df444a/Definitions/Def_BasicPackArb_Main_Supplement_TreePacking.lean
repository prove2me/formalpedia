-- Prove2me | Definitions.Def_BasicPackArb_Main_Supplement_TreePacking
-- name    : BasicPackArb_Main_Supplement_TreePacking
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:55:39.332309+00:00
-- url     : https://prove2.me/theorems/30f5f574-1985-4894-90e9-ddf5eb079ea1
-- title:
--   Matroid-rooted tree packings and partition connectedness
-- statement:
--   Let $M$ be a matroid on the finite root set $S$, let $k=r_M(S)$, and let $\pi:S\to V$ place the roots. Write $S_X=\pi^{-1}(X)$. A family $(T_s)_{s\in S}$ is an $M$-basic tree packing if the trees are edge-disjoint, $T_s$ is rooted at $\pi(s)$, and $\{s:v\in V(T_s)\}$ is a base of $M$ for every vertex $v$. The trees need not span $V$. Its edge union is the union over the entire root family.
--
--   The graph with roots is $M$-partition-connected precisely when, for every partition $\mathcal P$ into nonempty blocks,
--
--   $$k|\mathcal P|\le e_G(\mathcal P)+\sum_{X\in\mathcal P}r_M(S_X).$$
--
--   The rank helper converts the published extended-natural rank to a natural number on a finite carrier; it introduces no rank assumption. The inequality is evaluated over integers, with no truncated subtraction. These definitions connect the undirected results to the published independence and directed packing predicates.
-- source:
--   Durand de Gevigney, Nguyen, Szigeti, Basic Packing of Arborescences, arXiv:1207.1985v1, p. 2, §1

import Definitions.Def_BasicPackArb_Main_Supplement_Graph

set_option autoImplicit false
open scoped BigOperators

namespace BasicPackArb.Main.Supplement

/-- Finite matroid rank; every use is on a finite root carrier. -/
noncomputable def rank {S : Type} [Fintype S] (M : Matroid S) (Q : Set S) : ℕ :=
  (M.eRk Q).toNat

noncomputable def roots {V S : Type} [Fintype S] (π : S → V) (X : Finset V) : Finset S := by
  classical
  exact Finset.univ.filter (fun s => π s ∈ X)

/-- The additive integer form of the partition inequality on p. 2. -/
noncomputable def MPartitionConnected {V E S : Type} [Fintype V] [Fintype S]
    (G : Graph V E) (π : S → V) (M : Matroid S) : Prop :=
  ∀ P : Finset (Finset V), IsPartition P →
    (rank M Set.univ : ℤ) * P.card ≤
      (G.crossing P : ℤ) + ∑ X ∈ P, (rank M (π ⁻¹' (X : Set V)) : ℤ)

/-- Edge-disjoint, non-spanning trees; the roots covering each vertex form a base. -/
def IsTreePacking {V E S : Type} [DecidableEq E]
    (G : Graph V E) (π : S → V) (M : Matroid S) (T : S → RootedTree G) : Prop :=
  (∀ s, (T s).root = π s) ∧
  (∀ s t, s ≠ t → Disjoint (T s).edges (T t).edges) ∧
  (∀ v : V, M.IsBase {s | v ∈ (T s).verts})

noncomputable def treeUnion {V E S : Type} [DecidableEq E] [Fintype S]
    {G : Graph V E} (T : S → RootedTree G) : Finset E := by
  classical
  exact Finset.univ.biUnion (fun s => (T s).edges)

end BasicPackArb.Main.Supplement



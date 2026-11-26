-- Prove2me | Definitions.Def_C6BipartiteDomination_ExtremalResults
-- name    : C6BipartiteDomination_ExtremalResults
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T22:01:19.825986+00:00
-- url     : https://prove2.me/theorems/97896768-126c-4f2e-9773-6056d85c2bde
-- title:
--   Extremal Results
-- statement:
--   Definitions and structural lemmas for Extremal Results, from shouanrenhechun and contributors (shouanrenhechun/Myproofone; see pinned Apache-2.0 LICENSE and source headers)'s pinned Bipartite domination constant c_6 = 8/15 for graphs of maximum degree at most six development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Theorems.Thm_C6BipartiteDomination_exists_maximal_independent_subset

set_option autoImplicit true
namespace C6BipartiteDomination
open Finset
open Classical
noncomputable def coronaSelectedCore (D : Finset CoronaVertex) : Finset (Fin 5) :=
  Finset.univ.filter fun i => Sum.inl i ∈ D
noncomputable def coronaUnselectedCore (D : Finset CoronaVertex) : Finset (Fin 5) :=
  Finset.univ \ coronaSelectedCore D
noncomputable def coronaSelectedCoreVertices
    (D : Finset CoronaVertex) : Finset CoronaVertex :=
  (coronaSelectedCore D).image Sum.inl
noncomputable def coronaForcedLeaves
    (D : Finset CoronaVertex) : Finset CoronaVertex :=
  ((coronaUnselectedCore D).product Finset.univ).image
    (fun p : Fin 5 × Fin 2 => Sum.inr p)
variable {V : Type*} [Fintype V] [DecidableEq V]
theorem exists_bipartite_dominating_set (G : SimpleGraph V) :
    ∃ D : Finset V, IsBipartiteDominatingSet G D := by
  classical
  obtain ⟨I, hIuniv, hIind, hIdom⟩ :=
    exists_maximal_independent_subset G Finset.univ
  refine ⟨I, ?_⟩
  constructor
  · intro v hv
    obtain ⟨u, hu, hadj⟩ := hIdom (Finset.mem_univ v) hv
    exact ⟨u, hu, hadj⟩
  · refine ⟨fun _ => false, ?_⟩
    intro u v hu hv hadj
    exact (hIind hu hv hadj).elim
theorem exists_bipartite_dominating_card (G : SimpleGraph V) :
    ∃ n : ℕ, ∃ D : Finset V,
      IsBipartiteDominatingSet G D ∧ D.card = n := by
  obtain ⟨D, hD⟩ := exists_bipartite_dominating_set G
  exact ⟨D.card, D, hD, rfl⟩
noncomputable def gammaBip (G : SimpleGraph V) : ℕ :=
  Nat.find (exists_bipartite_dominating_card G)
structure FiniteSimpleGraphData where
  Vertex : Type
  finiteVertex : Fintype Vertex
  decidableVertex : DecidableEq Vertex
  graph : SimpleGraph Vertex
def C6Admissible (H : FiniteSimpleGraphData) : Prop := by
  letI := H.finiteVertex
  letI := H.decidableVertex
  exact HasNoIsolatedVertices H.graph ∧
    0 < Fintype.card H.Vertex ∧
    ∀ v, degreeTo H.graph Finset.univ v ≤ 6
noncomputable def finiteGraphDensity (H : FiniteSimpleGraphData) : ℝ := by
  letI := H.finiteVertex
  letI := H.decidableVertex
  exact (gammaBip H.graph : ℝ) / (Fintype.card H.Vertex : ℝ)
def C6DensitySet : Set ℝ :=
  {r | ∃ H : FiniteSimpleGraphData, C6Admissible H ∧ r = finiteGraphDensity H}
noncomputable def c6 : ℝ := sSup C6DensitySet
end C6BipartiteDomination



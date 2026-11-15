-- Prove2me | Definitions.Def_StableMSR_TightBlockSearch
-- name    : StableMSR_TightBlockSearch
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-14T17:19:31.841201+00:00
-- url     : https://prove2.me/theorems/afa9926e-5af7-44fe-878e-1458c80b1396
-- title:
--   External boundaries and recursive connected components
-- statement:
--   The external boundary of a finite vertex set consists of vertices outside it that have a neighbor inside it. For a candidate bag B and an interior C, children are the connected components of G minus B contained in C. These definitions specify the finite states of a tight-boundary decomposition search.
-- source:
--   Implementation-support definitions for finite bounded-treewidth decomposition search in the stable sum-of-radii clustering mission.

import Definitions.Def_Mazoit2013_PartialDecompositions
namespace StableMSR.Recovery.DecompositionSearch
open Havens PartialDecompositions
variable {V : Type} [Fintype V] [DecidableEq V]
noncomputable def boundary (G : SimpleGraph V) (C : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => v ∉ C ∧ ∃ u ∈ C, G.Adj u v)

lemma mem_boundary {G : SimpleGraph V} {C : Finset V} {v : V} :
    v ∈ boundary G C ↔ v ∉ C ∧ ∃ u ∈ C, G.Adj u v := by
  classical
  simp [boundary]

noncomputable def children (G : SimpleGraph V) (B C : Finset V) : Finset (Finset V) := by
  classical
  exact (PartialDecompositions.components G B).filter (fun D => D ⊆ C)

lemma mem_children {G : SimpleGraph V} {B C D : Finset V} :
    D ∈ children G B C ↔ IsFlap G B D ∧ D ⊆ C := by
  classical
  simp [children,mem_components]

end StableMSR.Recovery.DecompositionSearch



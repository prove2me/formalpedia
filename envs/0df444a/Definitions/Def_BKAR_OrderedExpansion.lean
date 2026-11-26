-- Prove2me | Definitions.Def_BKAR_OrderedExpansion
-- name    : BKAR_OrderedExpansion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:26:10.7418+00:00
-- url     : https://prove2.me/theorems/995be669-518c-5dc0-8266-f7c7f00f1521
-- title:
--   Ordered Expansion
-- statement:
--   Definitions and structural lemmas for Ordered Expansion, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Theorems.Thm_BKAR_EdgePath_IsPath_mono
import Theorems.Thm_BKAR_EdgePath_IsPath_mono_of_forall_mem
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_mono
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_mono_of_forall_mem
import Theorems.Thm_BKAR_Forest_not_mem_edges_of_mem_activeEdges
import Theorems.Thm_BKAR_Forest_pathInF_isSimple
import Theorems.Thm_BKAR_Forest_pathInF_unique
import Theorems.Thm_BKAR_IsAcyclicEdgeSet_mono

set_option autoImplicit false
namespace BKAR
namespace Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace EdgeExtension
variable {F F' : Forest V} {e₀ : Edge V}
end EdgeExtension
structure ActiveExtension (F : Forest V) (e : Edge V) where
  forest : Forest V
  extension : EdgeExtension F forest e
namespace ActiveExtension
variable {F : Forest V} {e : Edge V}
end ActiveExtension
theorem edgeExtension_of_edges_eq_insert
    {F F' : Forest V} {e₀ : Edge V}
    (he₀ : e₀ ∈ F.activeEdges)
    (hedges : F'.edges = insert e₀ F.edges) :
    EdgeExtension F F' e₀ := by
  let oldComponent :
      ∀ {i j : V}, F.inSameComponent i j → F'.inSameComponent i j := by
    intro i j h
    have hpathF : IsSimplePath F (F.pathInF i j h) i j :=
      F.pathInF_isSimple h
    have hgraphF :
        EdgePath.IsSimplePath F.edges (F.pathInF i j h) i j :=
      F.acyclic.isSimplePath_iff.mp hpathF
    have hgraphF' :
        EdgePath.IsSimplePath F'.edges (F.pathInF i j h) i j := by
      rw [hedges]
      exact hgraphF.mono (Finset.subset_insert e₀ F.edges)
    exact F'.inSameComponent_of_isSimplePath
      (F'.acyclic.isSimplePath_iff.mpr hgraphF')
  refine {
    new_not_mem := F.not_mem_edges_of_mem_activeEdges he₀
    edges_eq := hedges
    old_component := oldComponent
    old_path := ?_
    new_path_uses := ?_ }
  · intro i j h
    have hpathF : IsSimplePath F (F.pathInF i j h) i j :=
      F.pathInF_isSimple h
    have hgraphF :
        EdgePath.IsSimplePath F.edges (F.pathInF i j h) i j :=
      F.acyclic.isSimplePath_iff.mp hpathF
    have hgraphF' :
        EdgePath.IsSimplePath F'.edges (F.pathInF i j h) i j := by
      rw [hedges]
      exact hgraphF.mono (Finset.subset_insert e₀ F.edges)
    symm
    exact F'.pathInF_unique (oldComponent h) (F.pathInF i j h)
      (F'.acyclic.isSimplePath_iff.mpr hgraphF')
  · intro i j hnot hF'
    by_contra hmissing
    have hpathF' : IsSimplePath F' (F'.pathInF i j hF') i j :=
      F'.pathInF_isSimple hF'
    have hgraphF' :
        EdgePath.IsSimplePath F'.edges (F'.pathInF i j hF') i j :=
      F'.acyclic.isSimplePath_iff.mp hpathF'
    have hmemF : ∀ e ∈ F'.pathInF i j hF', e ∈ F.edges := by
      intro e he
      have heF' : e ∈ F'.edges :=
        hgraphF'.edge_mem e he
      have heInsert : e ∈ insert e₀ F.edges := by
        rw [← hedges]
        exact heF'
      rw [Finset.mem_insert] at heInsert
      exact heInsert.elim
        (fun heq => False.elim (hmissing (heq ▸ he)))
        id
    have hgraphF :
        EdgePath.IsSimplePath F.edges (F'.pathInF i j hF') i j :=
      hgraphF'.mono_of_forall_mem hmemF
    exact hnot (F.inSameComponent_of_isSimplePath
      (F.acyclic.isSimplePath_iff.mpr hgraphF))
def activeExtensionOfEdgesEqInsert
    {F F' : Forest V} {e₀ : Edge V}
    (he₀ : e₀ ∈ F.activeEdges)
    (hedges : F'.edges = insert e₀ F.edges) :
    ActiveExtension F e₀ where
  forest := F'
  extension := edgeExtension_of_edges_eq_insert he₀ hedges
end Forest
end BKAR



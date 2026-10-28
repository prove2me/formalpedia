-- Prove2me | Definitions.Def_BS2_b3ba934b_SelectedOrdinaryCaps
-- name    : BS2_b3ba934b_SelectedOrdinaryCaps
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:04:46.178456+00:00
-- url     : https://prove2.me/theorems/56aa8cfc-a971-4e64-93d8-657eb2808587
-- title:
--   Sensitivity separation: SelectedOrdinaryCaps (complete source module)
-- statement:
--   Complete Lean source module `SelectedOrdinaryCaps` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/SelectedOrdinaryCaps.lean; original SHA-256 1d1b46624051ea67fc1d5721f3eaf017c56d15c2b6547308a093bf5b6a3ace15; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Instantiate every ordinary transfer exclusion with the proved Paley-10007 label. -/
import Definitions.Def_BS2_b3ba934b_ArchivedExclusionBridge
import Definitions.Def_BS2_b3ba934b_Selected10007

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace ThreeBoundOrdinarySelected
open scoped Classical
noncomputable section
open ThreeBoundOrdinaryArchive

abbrev Adj := Sensitivity10007Labeling.Labeling10007.Adj

def tournament : ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament 10007 where
  Adj := Adj
  loopless := Sensitivity10007Labeling.Labeling10007.irreflexive
  edge_compl := fun {i j} h => Sensitivity10007Labeling.Labeling10007.edge_compl i j h

def label (v w : Fin 10007) : Fin 2 :=
  Sensitivity10007Labeling.Labeling10007.selectedLabel (v,w)

theorem ordinaryA_eq_cutoff (q : Fin 9) :
    Sensitivity10007Labeling.CompactLabeling10007.ordinaryA q = ZP.cutoff q.val := by
  fin_cases q <;> decide +kernel

theorem labelCaps : ZT.LabelCaps tournament label := by
  have h := Sensitivity10007Labeling.Labeling10007.selectedLabel_spec
  have ho (q : Fin 9) := ZT.ordinary_exclusion_defect_bound tournament label q.val
    (Sensitivity10007Labeling.CompactLabeling10007.ordinaryA q) (show
      ∀ I : ZL.OrdinaryIndex (Fin 10007) (Sensitivity10007Labeling.CompactLabeling10007.ordinaryA q),
        ¬ (ZL.ordinaryFamily Adj q.val (Sensitivity10007Labeling.CompactLabeling10007.ordinaryA q)).bad I
          (fun e => label e.1 e.2) from h.ordinary q)
  have hm (i : Fin 12) := ZT.marked_exclusion_card_bound tournament label
    (Sensitivity10007Labeling.CompactLabeling10007.marked i).q
    (Sensitivity10007Labeling.CompactLabeling10007.marked i).a
    (Sensitivity10007Labeling.CompactLabeling10007.marked i).m
    (Sensitivity10007Labeling.CompactLabeling10007.marked i).B (show
      ∀ I : ZL.MarkedIndex (Fin 10007)
          (Sensitivity10007Labeling.CompactLabeling10007.marked i).a
          (Sensitivity10007Labeling.CompactLabeling10007.marked i).m,
        ¬ (ZL.markedFamily Adj (Sensitivity10007Labeling.CompactLabeling10007.marked i).q
          (Sensitivity10007Labeling.CompactLabeling10007.marked i).a
          (Sensitivity10007Labeling.CompactLabeling10007.marked i).m
          (Sensitivity10007Labeling.CompactLabeling10007.marked i).B).bad I
          (fun e => label e.1 e.2) from h.marked i)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro q hq
    have hq' : q<9 := by omega
    simpa only [ordinaryA_eq_cutoff] using ho ⟨q,hq'⟩
  · exact ZT.source_exclusion_source_bound tournament label 20 h.source
  · exact ZT.dominator_exclusion_double_bound tournament label 18 h.dominator
  · intro q hq1 hq4
    interval_cases q
    · exact hm 0
    · exact hm 1
    · exact hm 2
    · exact hm 3
  · exact hm 4
  · exact hm 5
  · exact hm 6
  · exact hm 7
  · exact hm 8
  · exact hm 9
  · exact hm 10
  · exact hm 11

end
end ThreeBoundOrdinarySelected

#print axioms ThreeBoundOrdinarySelected.labelCaps



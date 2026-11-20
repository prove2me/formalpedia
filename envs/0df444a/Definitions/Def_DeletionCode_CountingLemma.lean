-- Prove2me | Definitions.Def_DeletionCode_CountingLemma
-- name    : DeletionCode_CountingLemma
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:17:08.581032+00:00
-- url     : https://prove2.me/theorems/a7d99102-d31f-4673-b9e8-07ddee89ee7c
-- title:
--   Counting Lemma
-- statement:
--   Definitions and structural lemmas for Counting Lemma, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CountingLemma.lean

import Definitions.Def_DeletionCode_SignedRuleCount
import Definitions.Def_DeletionCode_RuleSetGraph
import Definitions.Def_DeletionCode_CountExponent
import Theorems.Thm_DeletionCode_RuleSetGraph_componentCount_rulesOfFamily

set_option autoImplicit true
namespace DeletionCode.CountingLemma
open Windows HeaderRecovery GeneratingModel SignedSupport RuleReconstruction
open RuleSetGraph SignedRuleCount DescriptionCount CountExponent
def GeneratingSet (x : Letters) (n k ν R c : ℕ) (group : Fin ν → Fin R)
    (Q : RuleSet k) : Prop :=
  Q.card = R ∧ componentCount Q = c ∧
    ∃ E : EditedFamily (Fin ν) k,
      (∀ b, E.rank b = (group b).val) ∧
      BubbleGeometry E.family (windowLength k) ∧
      (∀ i, VertexDisjointOn E.family (windowLength k) (ruleBubbles E.family i)) ∧
      SignedGenerating E.family x n (windowLength k) ∧ rulesOfFamily E group = Q
theorem generatingSet_mem (x : Letters) (n k ν R c : ℕ) (group : Fin ν → Fin R)
    (Q : RuleSet k) (hQ : GeneratingSet x n k ν R c group Q) :
    GeneratingRuleSet x n k ν R c group Q := by
  obtain ⟨hcard, hc, E, hrank, H, hdis, hgen, hrules⟩ := hQ
  have hcomponents := componentCount_rulesOfFamily E group hrank H hdis
  have hcomponentCount : Fintype.card (SupportComponents.GraphComponents E.family (windowLength k)) = c := by
    rw [← hcomponents, hrules]
    exact hc
  exact ⟨E, hrank, H, hdis, hgen, hcomponentCount, hrules⟩
def generatingSetInclusion (x : Letters) (n k ν R c : ℕ) (group : Fin ν → Fin R) :
    {Q : RuleSet k // GeneratingSet x n k ν R c group Q} →
      {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q} :=
  fun Q => ⟨Q.val, generatingSet_mem x n k ν R c group Q.val Q.property⟩
end DeletionCode.CountingLemma



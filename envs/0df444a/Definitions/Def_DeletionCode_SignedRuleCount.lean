-- Prove2me | Definitions.Def_DeletionCode_SignedRuleCount
-- name    : DeletionCode_SignedRuleCount
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:16:04.071443+00:00
-- url     : https://prove2.me/theorems/06c1f6fc-c41c-457f-95bc-ff71e2536402
-- title:
--   Signed Rule Count
-- statement:
--   Definitions and structural lemmas for Signed Rule Count, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedRuleCount.lean

import Definitions.Def_DeletionCode_RuleReconstruction
import Definitions.Def_DeletionCode_GeneratingCount
import Theorems.Thm_DeletionCode_RuleReconstruction_rules_roundtrip
import Theorems.Thm_DeletionCode_SignedSupport_signed_generating_implies_generating

set_option autoImplicit true
namespace DeletionCode.SignedRuleCount
open Windows HeaderRecovery GeneratingModel SignedSupport RuleReconstruction
open RecordSerialization GeneratingCount DescriptionCount
abbrev RuleSet (k : ℕ) := Finset (Gram (windowLength k) → ℤ)
def GeneratingRuleSet (x : Letters) (n k ν R c : ℕ) (group : Fin ν → Fin R)
    (Q : RuleSet k) : Prop :=
  ∃ E : EditedFamily (Fin ν) k,
    (∀ b, E.rank b = (group b).val) ∧
    BubbleGeometry E.family (windowLength k) ∧
    (∀ i, VertexDisjointOn E.family (windowLength k) (ruleBubbles E.family i)) ∧
    SignedGenerating E.family x n (windowLength k) ∧
    Fintype.card (SupportComponents.GraphComponents E.family (windowLength k)) = c ∧
    rulesOfFamily E group = Q
theorem ruleSet_data_exists (x : Letters) (n k ν R c : ℕ) (group : Fin ν → Fin R)
    (Q : RuleSet k) (hQ : GeneratingRuleSet x n k ν R c group Q) :
    ∃ data : RecoveredData ν, GeneratingData x n k ν c data ∧ rulesOfData k group data = Q := by
  obtain ⟨E, _, H, hdis, hgen, hc, hQ⟩ := hQ
  have hg := signed_generating_implies_generating E.family x n (windowLength k) H hdis hgen
  exact ⟨dataOfFamily E, ⟨E, hg, hc, rfl⟩, (rules_roundtrip E group).trans hQ⟩
noncomputable def chooseRuleData (x : Letters) (n k ν R c : ℕ) (group : Fin ν → Fin R)
    (Q : {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q}) :
    {data : RecoveredData ν // GeneratingData x n k ν c data} :=
  ⟨Classical.choose (ruleSet_data_exists x n k ν R c group Q.val Q.property),
    (Classical.choose_spec (ruleSet_data_exists x n k ν R c group Q.val Q.property)).1⟩
end DeletionCode.SignedRuleCount



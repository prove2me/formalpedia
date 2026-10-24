-- Prove2me | Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part1Variable
-- name    : PricingWithTips3DM_188c204bbb0abeaa041ddea5Part1Variable
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T04:25:45.590082+00:00
-- url     : https://prove2.me/theorems/fc25487a-f2e5-4dd2-a300-70c6cf433de3
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesBounds.Part1.Lemma2.Variable
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part1Clause
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CLRS.Chapter34.Turing.TMClique
open PolyBuilder

theorem entry_variable_le_entry_length (entry : IndexedOccurrence × Nat) :
    occurrenceVariableCode entry.1.literal ≤
      (encodeIndexedOccurrenceEntry entry).length := by
  have h := value_le_encodeUnaryFrame_length
    (value := occurrenceVariableCode entry.1.literal)
    (values := indexedOccurrenceRowValues entry.2 entry.1)
    (by simp [indexedOccurrenceRowValues])
  simpa [encodeIndexedOccurrenceEntry] using
    h.trans (Nat.le_add_right (encodeUnaryFrame
      (indexedOccurrenceRowValues entry.2 entry.1)).length 1)

end CLRS.Chapter34.Turing.TMClique



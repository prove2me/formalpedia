-- Prove2me | Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part1Lemma2
-- name    : PricingWithTips3DM_188c204bbb0abeaa041ddea5Part1Lemma2
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T04:27:21.383301+00:00
-- url     : https://prove2.me/theorems/8c248f4a-db86-4cb6-b358-157138b64d8c
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesBounds.Part1.Lemma2
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part1Variable
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CLRS.Chapter34.Turing.TMClique
open PolyBuilder

theorem entry_fields_le_entries_length
    {entry : IndexedOccurrence × Nat}
    {entries : List (IndexedOccurrence × Nat)} (hentry : entry ∈ entries) :
    entry.2 ≤ (encodeIndexedOccurrenceEntries entries).length ∧
    entry.1.clauseIndex ≤ (encodeIndexedOccurrenceEntries entries).length ∧
    occurrenceVariableCode entry.1.literal ≤
      (encodeIndexedOccurrenceEntries entries).length := by
  have hlength := entry_length_le_entries_length hentry
  exact ⟨(entry_vertex_le_entry_length entry).trans hlength,
    (entry_clause_le_entry_length entry).trans hlength,
    (entry_variable_le_entry_length entry).trans hlength⟩
end CLRS.Chapter34.Turing.TMClique



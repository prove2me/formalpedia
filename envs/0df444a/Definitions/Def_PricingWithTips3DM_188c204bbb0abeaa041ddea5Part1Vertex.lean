-- Prove2me | Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part1Vertex
-- name    : PricingWithTips3DM_188c204bbb0abeaa041ddea5Part1Vertex
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T04:07:05.726363+00:00
-- url     : https://prove2.me/theorems/2736b489-3824-4866-b1d0-53acd6c7cdb6
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesBounds.Part1.Lemma2.Vertex
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part1Lemma1
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CLRS.Chapter34.Turing.TMClique
open PolyBuilder

theorem entry_vertex_le_entry_length (entry : IndexedOccurrence × Nat) :
    entry.2 ≤ (encodeIndexedOccurrenceEntry entry).length := by
  rcases entry with ⟨⟨clause, position, literal⟩, vertex⟩
  cases literal <;>
    simp [encodeIndexedOccurrenceEntry, indexedOccurrenceRowValues,
      encodeUnaryFrame_length, occurrencePolarityCode,
      occurrenceVariableCode] <;> omega

end CLRS.Chapter34.Turing.TMClique



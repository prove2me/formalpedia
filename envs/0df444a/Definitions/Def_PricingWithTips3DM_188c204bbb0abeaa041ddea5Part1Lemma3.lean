-- Prove2me | Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part1Lemma3
-- name    : PricingWithTips3DM_188c204bbb0abeaa041ddea5Part1Lemma3
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T04:55:28.244187+00:00
-- url     : https://prove2.me/theorems/eff10355-d864-45de-bfc2-0efb59871b5c
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesBounds.Part1.Lemma3
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_8fb65f62dc7f7936c2bf07db
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CLRS.Chapter34.Turing.TMClique
open PolyBuilder

theorem entries_length_le_encoding_length
    (entries : List (IndexedOccurrence × Nat)) :
    entries.length ≤ (encodeIndexedOccurrenceEntries entries).length := by
  rw [encodeIndexedOccurrenceEntries, List.length_flatMap]
  have hsum := List.length_le_sum_of_one_le
    (entries.map fun entry => (encodeIndexedOccurrenceEntry entry).length)
    (by
      intro length hlength
      rcases List.mem_map.mp hlength with ⟨entry, _, rfl⟩
      simp [encodeIndexedOccurrenceEntry])
  simpa using hsum
end CLRS.Chapter34.Turing.TMClique



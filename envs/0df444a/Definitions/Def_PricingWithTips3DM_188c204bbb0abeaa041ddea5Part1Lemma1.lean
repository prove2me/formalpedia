-- Prove2me | Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part1Lemma1
-- name    : PricingWithTips3DM_188c204bbb0abeaa041ddea5Part1Lemma1
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T03:11:53.942049+00:00
-- url     : https://prove2.me/theorems/3cb9115d-c292-42eb-88f6-03eec2ce41a7
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesBounds.Part1.Lemma1
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_8fb65f62dc7f7936c2bf07db
import Mathlib.Tactic
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CLRS.Chapter34.Turing.TMClique
open PolyBuilder

theorem entry_length_le_entries_length
    {entry : IndexedOccurrence × Nat}
    {entries : List (IndexedOccurrence × Nat)} (hentry : entry ∈ entries) :
    (encodeIndexedOccurrenceEntry entry).length ≤
      (encodeIndexedOccurrenceEntries entries).length := by
  have hmem : (encodeIndexedOccurrenceEntry entry).length ∈
      entries.map (fun current =>
        (encodeIndexedOccurrenceEntry current).length) := by
    exact List.mem_map.mpr ⟨entry, hentry, rfl⟩
  have hsum := List.le_sum_of_mem hmem
  simpa [encodeIndexedOccurrenceEntries, List.length_flatMap] using hsum
end CLRS.Chapter34.Turing.TMClique



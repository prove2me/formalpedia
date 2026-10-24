-- Prove2me | Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part3Symbols
-- name    : PricingWithTips3DM_188c204bbb0abeaa041ddea5Part3Symbols
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T05:27:30.036444+00:00
-- url     : https://prove2.me/theorems/1404003b-aacb-4084-aad2-7f804dac7969
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesBounds.Part3.Fixed.Symbols
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part2
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CLRS.Chapter34.Turing.TMClique
open PolyBuilder

theorem outer_iteration_symbols_length_le
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat)) :
    (encodeReversedOccurrenceEntries priors.reverse).length ≤
      (encodeIndexedOccurrenceEntries (current :: priors)).length := by
  rw [encodeReversedOccurrenceEntries_length,
    encodeIndexedOccurrenceEntries_reverse_length]
  simp [encodeIndexedOccurrenceEntries]

end CLRS.Chapter34.Turing.TMClique



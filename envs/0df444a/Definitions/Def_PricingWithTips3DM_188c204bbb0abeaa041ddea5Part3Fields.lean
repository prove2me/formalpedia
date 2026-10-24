-- Prove2me | Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part3Fields
-- name    : PricingWithTips3DM_188c204bbb0abeaa041ddea5Part3Fields
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T05:41:08.968336+00:00
-- url     : https://prove2.me/theorems/25ca1da5-dcf7-4388-86dd-a83f36099530
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesBounds.Part3.Fixed.Fields
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part2
import Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part3Arithmetic
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CLRS.Chapter34.Turing.TMClique
open PolyBuilder

theorem outer_iteration_fields_steps_le
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat)) :
    1 + (current.1.clauseIndex + occurrenceVariableCode current.1.literal + 2) +
        current.2 + 3 ≤
      3 * (encodeIndexedOccurrenceEntries (current :: priors)).length + 6 := by
  have hcurrent : current ∈ current :: priors := by simp
  have hfields := entry_fields_le_entries_length hcurrent
  rcases hfields with ⟨hvertex, hclause, hvariable⟩
  exact PricingWithTips3DM_outer_iteration_three_fields
    hclause hvariable hvertex

end CLRS.Chapter34.Turing.TMClique



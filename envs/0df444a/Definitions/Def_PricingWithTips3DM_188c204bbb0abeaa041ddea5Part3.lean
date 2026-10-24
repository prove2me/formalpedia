-- Prove2me | Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part3
-- name    : PricingWithTips3DM_188c204bbb0abeaa041ddea5Part3
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T05:43:10.335084+00:00
-- url     : https://prove2.me/theorems/1c634dcd-d449-448f-b957-4fde620e6f53
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesBounds.Part3
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part3Scan
import Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part3Restore
import Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part3Emit
import Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part3Fixed
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CLRS.Chapter34.Turing.TMClique
open PolyBuilder

theorem outer_iteration_steps_le
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat)) :
    compatibilityEdgesOuterIterationSteps current priors ≤
      70 * ((encodeIndexedOccurrenceEntries (current :: priors)).length + 1) ^ 2 := by
  let entries := current :: priors
  let bound := (encodeIndexedOccurrenceEntries entries).length
  have hscan := outer_iteration_scan_steps_le current priors
  have hrestore := outer_iteration_restore_steps_le current priors
  have hemit := outer_iteration_emit_steps_le current priors
  have hfixed := outer_iteration_fixed_steps_le current priors
  have hpositive : 1 ≤ bound := by
    have hcurrent : current ∈ entries := by simp [entries]
    have hlength := entry_length_le_entries_length hcurrent
    have hone : 1 ≤ (encodeIndexedOccurrenceEntry current).length := by
      simp [encodeIndexedOccurrenceEntry]
    exact hone.trans hlength
  simp only [compatibilityEdgesOuterIterationSteps]
  change _ ≤ 70 * (bound + 1) ^ 2
  nlinarith
end CLRS.Chapter34.Turing.TMClique



-- Prove2me | Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part3Restore
-- name    : PricingWithTips3DM_188c204bbb0abeaa041ddea5Part3Restore
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T05:17:51.785464+00:00
-- url     : https://prove2.me/theorems/4596cd5f-31d1-426c-a259-87647c9891fa
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesBounds.Part3.Restore
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

theorem outer_iteration_restore_steps_le
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat)) :
    compatibilityEdgesRestoreTaggedRowsSteps priors.reverse ≤
      9 * (encodeIndexedOccurrenceEntries (current :: priors)).length *
          ((encodeIndexedOccurrenceEntries (current :: priors)).length + 1) + 1 := by
  let entries := current :: priors
  let bound := (encodeIndexedOccurrenceEntries entries).length
  have hrestoreEach : ∀ prior ∈ priors.reverse,
      compatibilityEdgesRestoreTaggedRowSteps prior + 1 ≤
        9 * (bound + 1) := by
    intro prior hprior
    have hprior' : prior ∈ priors := by simpa using hprior
    have hmem : prior ∈ entries := by simp [entries, hprior']
    have hrestore := restore_steps_le hmem
    change compatibilityEdgesRestoreTaggedRowSteps prior ≤
      8 * (bound + 1) at hrestore
    omega
  have hrestoreSum := sum_map_le_mul priors.reverse
    (fun prior => compatibilityEdgesRestoreTaggedRowSteps prior + 1)
    (9 * (bound + 1)) hrestoreEach
  have hentriesLength := entries_length_le_encoding_length entries
  have hpriorsLength : priors.length ≤ bound := by
    change entries.length ≤ bound at hentriesLength
    simp only [entries, List.length_cons] at hentriesLength
    omega
  have hreverseLength : priors.reverse.length ≤ bound := by
    simpa using hpriorsLength
  simp only [compatibilityEdgesRestoreTaggedRowsSteps]
  change _ ≤ 9 * bound * (bound + 1) + 1
  nlinarith

end CLRS.Chapter34.Turing.TMClique



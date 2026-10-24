-- Prove2me | Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part3Emit
-- name    : PricingWithTips3DM_188c204bbb0abeaa041ddea5Part3Emit
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T05:18:37.9285+00:00
-- url     : https://prove2.me/theorems/20e954a9-9098-41bc-8af1-9459fa9edcbe
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesBounds.Part3.Emit
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

theorem outer_iteration_emit_steps_le
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat)) :
    compatibilityEdgesEmitPriorRowsSteps current priors ≤
      20 * (encodeIndexedOccurrenceEntries (current :: priors)).length *
        ((encodeIndexedOccurrenceEntries (current :: priors)).length + 1) := by
  let entries := current :: priors
  let bound := (encodeIndexedOccurrenceEntries entries).length
  have hcurrent : current ∈ entries := by simp [entries]
  have hemitEach : ∀ prior ∈ priors,
      compatibilityEdgesEmitPriorRowSteps current prior ≤
        20 * (bound + 1) := by
    intro prior hprior
    have hmem : prior ∈ entries := by simp [entries, hprior]
    simpa [bound] using emit_prior_steps_le hcurrent hmem
  have hemitSum := sum_map_le_mul priors
    (compatibilityEdgesEmitPriorRowSteps current) (20 * (bound + 1))
    hemitEach
  have hentriesLength := entries_length_le_encoding_length entries
  have hpriorsLength : priors.length ≤ bound := by
    change entries.length ≤ bound at hentriesLength
    simp only [entries, List.length_cons] at hentriesLength
    omega
  simp only [compatibilityEdgesEmitPriorRowsSteps]
  change _ ≤ 20 * bound * (bound + 1)
  nlinarith

end CLRS.Chapter34.Turing.TMClique



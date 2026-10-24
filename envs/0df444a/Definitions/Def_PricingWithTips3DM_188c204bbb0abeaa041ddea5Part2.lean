-- Prove2me | Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part2
-- name    : PricingWithTips3DM_188c204bbb0abeaa041ddea5Part2
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T05:00:43.459429+00:00
-- url     : https://prove2.me/theorems/5cce6b41-5ccb-4b40-bb3e-513b9c02befa
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesBounds.Part2
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part1
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CLRS.Chapter34.Turing.TMClique
open PolyBuilder

theorem current_steps_le {entry : IndexedOccurrence × Nat}
    {entries : List (IndexedOccurrence × Nat)} (hentry : entry ∈ entries) :
    compatibilityEdgesCurrentRowSteps entry ≤
      10 * ((encodeIndexedOccurrenceEntries entries).length + 1) := by
  have hfields := entry_fields_le_entries_length hentry
  rcases entry with ⟨⟨clause, position, literal⟩, vertex⟩
  cases literal <;>
    simp [compatibilityEdgesCurrentRowSteps, occurrencePolarityFlag,
      occurrenceVariableCode] at * <;> omega

theorem prior_steps_le
    {current prior : IndexedOccurrence × Nat}
    {entries : List (IndexedOccurrence × Nat)}
    (hcurrent : current ∈ entries) (hprior : prior ∈ entries) :
    compatibilityEdgesPriorRowSteps current prior ≤
      30 * ((encodeIndexedOccurrenceEntries entries).length + 1) := by
  have hc := entry_fields_le_entries_length hcurrent
  have hp := entry_fields_le_entries_length hprior
  rcases current with ⟨⟨cc, cpos, clit⟩, cv⟩
  rcases prior with ⟨⟨pc, ppos, plit⟩, pv⟩
  cases clit <;> cases plit <;>
    simp [compatibilityEdgesPriorRowSteps,
      compatibilityEdgesComparisonSteps, occurrencePolarityFlag,
      occurrenceVariableCode] at * <;> omega


theorem restore_steps_le
    {prior : IndexedOccurrence × Nat}
    {entries : List (IndexedOccurrence × Nat)} (hprior : prior ∈ entries) :
    compatibilityEdgesRestoreTaggedRowSteps prior ≤
      8 * ((encodeIndexedOccurrenceEntries entries).length + 1) := by
  have hp := entry_fields_le_entries_length hprior
  rcases prior with ⟨⟨pc, ppos, plit⟩, pv⟩
  cases plit <;>
    simp [compatibilityEdgesRestoreTaggedRowSteps,
      occurrencePolarityCode, occurrenceVariableCode] at * <;> omega

theorem emit_flagged_steps_le
    {prior : IndexedOccurrence × Nat}
    {entries : List (IndexedOccurrence × Nat)} (hprior : prior ∈ entries) :
    compatibilityEdgesEmitFlaggedRowSteps prior ≤
      8 * ((encodeIndexedOccurrenceEntries entries).length + 1) := by
  have hp := entry_fields_le_entries_length hprior
  rcases prior with ⟨⟨pc, ppos, plit⟩, pv⟩
  cases plit <;>
    simp [compatibilityEdgesEmitFlaggedRowSteps,
      occurrencePolarityCode, occurrenceVariableCode] at * <;> omega

theorem emit_edge_steps_le
    {current prior : IndexedOccurrence × Nat}
    {entries : List (IndexedOccurrence × Nat)}
    (hcurrent : current ∈ entries) (hprior : prior ∈ entries) :
    compatibilityEdgesEmitCompatibleEdgeSteps current.2 prior.2 ≤
      10 * ((encodeIndexedOccurrenceEntries entries).length + 1) := by
  have hc := entry_fields_le_entries_length hcurrent
  have hp := entry_fields_le_entries_length hprior
  simp only [compatibilityEdgesEmitCompatibleEdgeSteps]
  omega

theorem emit_prior_steps_le
    {current prior : IndexedOccurrence × Nat}
    {entries : List (IndexedOccurrence × Nat)}
    (hcurrent : current ∈ entries) (hprior : prior ∈ entries) :
    compatibilityEdgesEmitPriorRowSteps current prior ≤
      20 * ((encodeIndexedOccurrenceEntries entries).length + 1) := by
  have hscan := emit_flagged_steps_le hprior
  have hedge := emit_edge_steps_le hcurrent hprior
  have hp := entry_fields_le_entries_length hprior
  simp only [compatibilityEdgesEmitPriorRowSteps]
  split <;> omega


theorem encodeReversedOccurrenceEntries_length
    (entries : List (IndexedOccurrence × Nat)) :
    (encodeReversedOccurrenceEntries entries).length =
      (encodeIndexedOccurrenceEntries entries).length := by
  induction entries with
  | nil => simp [encodeReversedOccurrenceEntries,
      encodeIndexedOccurrenceEntries]
  | cons entry entries ih =>
      simp [encodeReversedOccurrenceEntries,
        encodeIndexedOccurrenceEntries]

/-- Reversing a row family preserves its serialized unary length. -/
theorem encodeIndexedOccurrenceEntries_reverse_length
    (entries : List (IndexedOccurrence × Nat)) :
    (encodeIndexedOccurrenceEntries entries.reverse).length =
      (encodeIndexedOccurrenceEntries entries).length := by
  simp [encodeIndexedOccurrenceEntries, List.length_flatMap,
    List.map_reverse]
end CLRS.Chapter34.Turing.TMClique



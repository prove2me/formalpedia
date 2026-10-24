-- Prove2me | Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part5
-- name    : PricingWithTips3DM_188c204bbb0abeaa041ddea5Part5
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T05:46:43.423061+00:00
-- url     : https://prove2.me/theorems/3d96d2a6-2799-4ef5-8d55-d9125b6a5f6d
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesBounds.Part5
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part4
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CLRS.Chapter34.Turing.TMClique
open PolyBuilder

/-- The complete outer-loop family has a cubic bound in the actual serialized
row-family length. -/
theorem compatibilityEdgesOuterIterationsSteps_le_input
    (entries : List (IndexedOccurrence × Nat)) :
    compatibilityEdgesOuterIterationsSteps entries ≤
      70 * ((encodeIndexedOccurrenceEntries entries).length + 1) ^ 3 := by
  have hsteps := outer_iterations_steps_le_mul entries
  have hlength := entries_length_le_encoding_length entries
  have hsquare : 0 ≤
      ((encodeIndexedOccurrenceEntries entries).length + 1) ^ 2 :=
    Nat.zero_le _
  nlinarith


/-- Loading an arbitrary well-shaped row family is linear in its serialized
length. -/
theorem compatibilityEdgesLoadRowsSteps_le_input
    (entries : List (IndexedOccurrence × Nat)) :
    compatibilityEdgesLoadRowsSteps entries ≤
      4 * ((encodeIndexedOccurrenceEntries entries).length + 1) := by
  induction entries with
  | nil => simp [compatibilityEdgesLoadRowsSteps,
      encodeIndexedOccurrenceEntries]
  | cons entry entries ih =>
      change (entries.map compatibilityEdgesLoadRowSteps).sum ≤
        4 * ((entries.flatMap encodeIndexedOccurrenceEntry).length + 1) at ih
      have hrow : 1 ≤ (encodeIndexedOccurrenceEntry entry).length := by
        rcases entry with ⟨⟨clause, position, literal⟩, vertex⟩
        cases literal <;>
          simp [encodeIndexedOccurrenceEntry, indexedOccurrenceRowValues,
            encodeUnaryFrame_length, occurrencePolarityCode,
            occurrenceVariableCode]
      simp only [compatibilityEdgesLoadRowsSteps, List.map_cons,
        List.sum_cons, compatibilityEdgesLoadRowSteps,
        encodeIndexedOccurrenceEntries, List.flatMap_cons,
        List.length_append]
      omega

/-- The whole terminating compatibility controller has a cubic bound in the
actual canonical row input consumed by the fixed program. -/
theorem compatibilityEdgesSteps_le_input (formula : CNF) :
    compatibilityEdgesSteps formula ≤
      80 * ((encodeIndexedOccurrenceRows formula).length + 1) ^ 3 := by
  let entries := (indexedOccurrences formula).zipIdx
  let inputLength := (encodeIndexedOccurrenceRows formula).length
  have hencoding :
      (encodeIndexedOccurrenceEntries entries).length = inputLength := by
    simp [entries, inputLength, encodeIndexedOccurrenceEntries_zipIdx]
  have hreverse :
      (encodeIndexedOccurrenceEntries entries.reverse).length = inputLength := by
    rw [encodeIndexedOccurrenceEntries_reverse_length, hencoding]
  have hload := compatibilityEdgesLoadRowsSteps_le_input entries
  rw [hencoding] at hload
  have houter := compatibilityEdgesOuterIterationsSteps_le_input entries.reverse
  rw [hreverse] at houter
  have hlinear : inputLength + 1 ≤ (inputLength + 1) ^ 3 :=
    Nat.le_pow (by omega)
  simp only [compatibilityEdgesSteps]
  change compatibilityEdgesLoadRowsSteps entries +
      compatibilityEdgesOuterIterationsSteps entries.reverse + 3 ≤
    80 * (inputLength + 1) ^ 3
  nlinarith
end CLRS.Chapter34.Turing.TMClique



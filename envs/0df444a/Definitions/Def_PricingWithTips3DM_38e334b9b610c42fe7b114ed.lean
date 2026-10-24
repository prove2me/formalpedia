-- Prove2me | Definitions.Def_PricingWithTips3DM_38e334b9b610c42fe7b114ed
-- name    : PricingWithTips3DM_38e334b9b610c42fe7b114ed
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T02:21:07.299241+00:00
-- url     : https://prove2.me/theorems/ba8e6c81-bf52-42ae-8879-f2025a88ca2a
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesGenericRun
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_605d537983b61208617f371b
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Generic terminating run of the occurrence-row pair controller

The compatibility controller is useful beyond the 3-CNF occurrence graph.
This module exposes its actual reusable boundary: an arbitrary family of
four-field indexed-occurrence rows.  The earlier formula-specific theorem is
an immediate specialization of this run.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.TMClique

open PolyBuilder

/-- Exact step budget for the compatibility controller on an arbitrary
explicit row family. -/
def compatibilityEdgesEntriesSteps
    (entries : List (IndexedOccurrence × Nat)) : Nat :=
  compatibilityEdgesLoadRowsSteps entries +
    compatibilityEdgesOuterIterationsSteps entries.reverse + 3

/-- The fixed compatibility controller consumes any canonical four-field row
family, emits its compatible endpoint pairs, clears all scratch state, and
halts. -/
def compatibilityEdges_entriesRun
    (entries : List (IndexedOccurrence × Nat)) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (initialCfg compatibilityEdgesProgram
        (encodeIndexedOccurrenceEntries entries))
      (some (haltCfg compatibilityEdgesProgram
        (encodeCompatibleOccurrenceIterations entries.reverse)))
      (compatibilityEdgesEntriesSteps entries) := by
  rcases compatibilityEdges_loadRowsCleanRun
      entries [] [] [] none false 0 0 0 with
    ⟨finalBuffer₁, loadedRows⟩
  have enterOuter : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .load finalBuffer₁ none false [] []
        (encodeIndexedOccurrenceEntries entries.reverse) [] 0 0 0)
      (some (compatibilityEdgesCfg .outer none none false [] []
        (encodeIndexedOccurrenceEntries entries.reverse) [] 0 0 0)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have loaded : EvalsToInTime (step compatibilityEdgesProgram)
      (initialCfg compatibilityEdgesProgram
        (encodeIndexedOccurrenceEntries entries))
      (some (compatibilityEdgesCfg .outer none none false [] []
        (encodeIndexedOccurrenceEntries entries.reverse) [] 0 0 0))
      (compatibilityEdgesLoadRowsSteps entries + 1) := by
    let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
      (compatibilityEdgesLoadRowsSteps entries) 1 _ _ _
      loadedRows (by simpa using enterOuter)
    simpa [initialCfg, compatibilityEdgesCfg, compatibilityEdgesProgram,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full
  have iterations := compatibilityEdges_outerIterationsRun
    entries.reverse []
  have stop : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .outer none none false []
        (encodeCompatibleOccurrenceIterations entries.reverse)
        [] [] 0 0 0)
      (some (compatibilityEdgesCfg .halt none none false []
        (encodeCompatibleOccurrenceIterations entries.reverse)
        [] [] 0 0 0)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have halt : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .halt none none false []
        (encodeCompatibleOccurrenceIterations entries.reverse)
        [] [] 0 0 0)
      (some (haltCfg compatibilityEdgesProgram
        (encodeCompatibleOccurrenceIterations entries.reverse))) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let afterIterations := EvalsToInTime.trans
    (step compatibilityEdgesProgram)
    (compatibilityEdgesLoadRowsSteps entries + 1)
    (compatibilityEdgesOuterIterationsSteps entries.reverse)
    _ _ _ loaded iterations
  let stopped := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ 1 _ _ _ afterIterations (by simpa using stop)
  let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ 1 _ _ _ stopped halt
  convert full using 1
  simp only [compatibilityEdgesEntriesSteps]
  omega

end CLRS.Chapter34.Turing.TMClique



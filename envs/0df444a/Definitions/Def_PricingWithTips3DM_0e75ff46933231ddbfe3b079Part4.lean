-- Prove2me | Definitions.Def_PricingWithTips3DM_0e75ff46933231ddbfe3b079Part4
-- name    : PricingWithTips3DM_0e75ff46933231ddbfe3b079Part4
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T22:08:48.651187+00:00
-- url     : https://prove2.me/theorems/cc97178d-bc1b-4e3a-9aef-26bd39faa40d
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesPriorRows.Part4
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_0e75ff46933231ddbfe3b079Part3
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- Every prior row is scanned once.  Rows are moved to work two in reverse
family order, each row is reversed physically, and each receives the exact
Boolean compatibility tag. -/
def compatibilityEdges_priorRowsRun
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat))
    (tail work₂ : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool) :
    Σ finalBuffer₁ : Option UnaryFrameSym,
      Σ finalBuffer₂ : Option UnaryFrameSym,
        Σ finalTest : Bool,
          EvalsToInTime (step compatibilityEdgesProgram)
            (compatibilityEdgesCfg
              (.priorStart (occurrencePolarityFlag current.1.literal))
              buffer₁ buffer₂ test [] output
              (encodeIndexedOccurrenceEntries priors ++ tail) work₂
              current.2 current.1.clauseIndex
              (occurrenceVariableCode current.1.literal))
            (some (compatibilityEdgesCfg
              (.priorStart (occurrencePolarityFlag current.1.literal))
              finalBuffer₁ finalBuffer₂ finalTest [] output tail
              (encodeTaggedOccurrenceEntries current priors.reverse ++ work₂)
              current.2 current.1.clauseIndex
              (occurrenceVariableCode current.1.literal)))
            (compatibilityEdgesPriorRowsSteps current priors) := by
  induction priors generalizing buffer₁ buffer₂ test work₂ with
  | nil =>
      exact ⟨buffer₁, buffer₂, test, ⟨⟨0, by
        simp [encodeIndexedOccurrenceEntries,
          encodeTaggedOccurrenceEntries]⟩, le_rfl⟩⟩
  | cons prior priors ih =>
      let remaining := encodeIndexedOccurrenceEntries priors ++ tail
      have first := compatibilityEdges_priorRowRun current prior remaining
        work₂ output buffer₁ buffer₂ test
      rcases ih (buffer₁ := some .frameEnd) (buffer₂ := none)
          (test := decide (occurrenceVariableCode prior.1.literal <
            occurrenceVariableCode current.1.literal))
          (work₂ := encodeTaggedOccurrenceEntry current prior ++ work₂) with
        ⟨finalBuffer₁, finalBuffer₂, finalTest, rest⟩
      refine ⟨finalBuffer₁, finalBuffer₂, finalTest, ?_⟩
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        (compatibilityEdgesPriorRowSteps current prior)
        (compatibilityEdgesPriorRowsSteps current priors) _ _ _ first rest
      simpa [remaining, encodeIndexedOccurrenceEntries,
        encodeTaggedOccurrenceEntries, encodeTaggedOccurrenceEntry,
        compatibilityEdgesPriorRowsSteps, List.reverse_cons,
        List.flatMap_append, List.append_assoc, Nat.add_assoc,
        Nat.add_comm] using full
end TMClique
end Turing
end Chapter34
end CLRS



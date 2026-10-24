-- Prove2me | Definitions.Def_PricingWithTips3DM_114cb9bce6cb86acfefc9202Part4FieldTail
-- name    : PricingWithTips3DM_114cb9bce6cb86acfefc9202Part4FieldTail
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T00:08:58.391135+00:00
-- url     : https://prove2.me/theorems/dd06e75b-88f9-45a4-ace9-e842d2512bc8
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesRestoreRow.Part4.Fields.FieldTail
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_114cb9bce6cb86acfefc9202Part4FieldHead
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition
namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique
open PolyBuilder

def compatibilityEdges_restoreTaggedRowFieldTailRun
    (priorClause priorVertex : Nat) (priorLiteral : Literal)
    (rowFlag : UnaryFrameSym) (input work₁ tail : List UnaryFrameSym)
    (output : List CliqueSym) (buffer₁ : Option UnaryFrameSym)
    (test : Bool) (upper : Nat) :
    Σ finalBuffer₂ : Option UnaryFrameSym,
      EvalsToInTime (step compatibilityEdgesProgram)
        (compatibilityEdgesCfg .taggedRestoreClause buffer₁ (some .separator)
          test input output
          (.separator :: List.replicate (occurrencePolarityFlag priorLiteral).toNat .tick ++
            .separator :: List.replicate (occurrenceVariableCode priorLiteral) .tick ++
              .separator :: .frameEnd :: rowFlag :: work₁)
          (List.replicate priorClause .tick ++ .separator ::
            List.replicate priorVertex .tick ++ tail) upper 0 0)
        (some (compatibilityEdgesCfg .taggedRestoreVertex buffer₁ finalBuffer₂
          test input output
          (List.replicate priorVertex .tick ++ .separator ::
            List.replicate priorClause .tick ++ .separator ::
              List.replicate (occurrencePolarityFlag priorLiteral).toNat .tick ++ .separator ::
                List.replicate (occurrenceVariableCode priorLiteral) .tick ++
                  .separator :: .frameEnd :: rowFlag :: work₁)
          tail upper 0 0)) (2 * priorVertex + (priorClause + 1)) := by
  have clauseRun := compatibilityEdges_restoreFieldRun .clause priorClause input
    (.separator :: List.replicate (occurrencePolarityFlag priorLiteral).toNat .tick ++
      .separator :: List.replicate (occurrenceVariableCode priorLiteral) .tick ++
        .separator :: .frameEnd :: rowFlag :: work₁)
    (List.replicate priorVertex .tick ++ tail)
    output buffer₁ (some .separator) test upper
  have vertexRun := compatibilityEdges_restoreVertexTicksRun priorVertex input
    (.separator :: List.replicate priorClause .tick ++ .separator ::
      List.replicate (occurrencePolarityFlag priorLiteral).toNat .tick ++ .separator ::
        List.replicate (occurrenceVariableCode priorLiteral) .tick ++
          .separator :: .frameEnd :: rowFlag :: work₁)
    tail output buffer₁ (some .separator) test upper
  refine ⟨if priorVertex = 0 then some .separator else some .tick, ?_⟩
  exact EvalsToInTime.trans (step compatibilityEdgesProgram) _ _ _ _ _
    (by simpa [compatibilityRestoreFieldLabel, compatibilityRestoreFieldNext,
      List.append_assoc] using clauseRun)
    (by simpa [List.append_assoc] using vertexRun)

end TMClique
end Turing
end Chapter34
end CLRS



-- Prove2me | Definitions.Def_PricingWithTips3DM_114cb9bce6cb86acfefc9202Part4FieldHead
-- name    : PricingWithTips3DM_114cb9bce6cb86acfefc9202Part4FieldHead
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T00:04:04.588806+00:00
-- url     : https://prove2.me/theorems/7f8aba03-45d8-4a28-8b93-e9da8a3a3540
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesRestoreRow.Part4.Fields.FieldHead
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_114cb9bce6cb86acfefc9202Part4Prefix
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition
namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique
open PolyBuilder

def compatibilityEdges_restoreTaggedRowFieldHeadRun
    (priorClause priorVertex : Nat) (priorLiteral : Literal)
    (rowFlag : UnaryFrameSym) (input work₁ tail : List UnaryFrameSym)
    (output : List CliqueSym) (buffer₁ : Option UnaryFrameSym)
    (test : Bool) (upper : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .taggedRestoreVariable buffer₁ (some .separator)
        test input output (.separator :: .frameEnd :: rowFlag :: work₁)
        (List.replicate (occurrenceVariableCode priorLiteral) .tick ++ .separator ::
          List.replicate (occurrencePolarityFlag priorLiteral).toNat .tick ++ .separator ::
            List.replicate priorClause .tick ++ .separator ::
              List.replicate priorVertex .tick ++ tail) upper 0 0)
      (some (compatibilityEdgesCfg .taggedRestoreClause buffer₁ (some .separator)
        test input output
        (.separator :: List.replicate (occurrencePolarityFlag priorLiteral).toNat .tick ++
          .separator :: List.replicate (occurrenceVariableCode priorLiteral) .tick ++
            .separator :: .frameEnd :: rowFlag :: work₁)
        (List.replicate priorClause .tick ++ .separator ::
          List.replicate priorVertex .tick ++ tail) upper 0 0))
      (((occurrencePolarityFlag priorLiteral).toNat + 1) +
        (occurrenceVariableCode priorLiteral + 1)) := by
  have variableRun := compatibilityEdges_restoreFieldRun .variable
    (occurrenceVariableCode priorLiteral) input
    (.separator :: .frameEnd :: rowFlag :: work₁)
    (List.replicate (occurrencePolarityFlag priorLiteral).toNat .tick ++ .separator ::
      List.replicate priorClause .tick ++ .separator :: List.replicate priorVertex .tick ++ tail)
    output buffer₁ (some .separator) test upper
  have polarityRun := compatibilityEdges_restoreFieldRun .polarity
    (occurrencePolarityFlag priorLiteral).toNat input
    (.separator :: List.replicate (occurrenceVariableCode priorLiteral) .tick ++
      .separator :: .frameEnd :: rowFlag :: work₁)
    (List.replicate priorClause .tick ++ .separator :: List.replicate priorVertex .tick ++ tail)
    output buffer₁ (some .separator) test upper
  exact EvalsToInTime.trans (step compatibilityEdgesProgram) _ _ _ _ _
    (by simpa [compatibilityRestoreFieldLabel, compatibilityRestoreFieldNext,
      List.append_assoc] using variableRun)
    (by simpa [compatibilityRestoreFieldLabel, compatibilityRestoreFieldNext,
      List.append_assoc] using polarityRun)

end TMClique
end Turing
end Chapter34
end CLRS



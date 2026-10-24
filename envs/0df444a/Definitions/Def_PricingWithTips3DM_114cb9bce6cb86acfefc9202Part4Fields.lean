-- Prove2me | Definitions.Def_PricingWithTips3DM_114cb9bce6cb86acfefc9202Part4Fields
-- name    : PricingWithTips3DM_114cb9bce6cb86acfefc9202Part4Fields
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T00:13:21.555232+00:00
-- url     : https://prove2.me/theorems/bd85351e-3b66-41c9-ac78-7cffe9d3f175
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesRestoreRow.Part4.Fields
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_114cb9bce6cb86acfefc9202Part4FieldTail
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition
namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique
open PolyBuilder

def compatibilityEdges_restoreTaggedRowFieldsRun
    (priorClause priorVertex : Nat) (priorLiteral : Literal)
    (rowFlag : UnaryFrameSym) (input work₁ tail : List UnaryFrameSym)
    (output : List CliqueSym) (buffer₁ : Option UnaryFrameSym)
    (test : Bool) (upper : Nat) :
    Σ finalBuffer₂ : Option UnaryFrameSym,
      EvalsToInTime (step compatibilityEdgesProgram)
        (compatibilityEdgesCfg .taggedRestoreVariable buffer₁ (some .separator)
          test input output (.separator :: .frameEnd :: rowFlag :: work₁)
          (List.replicate (occurrenceVariableCode priorLiteral) .tick ++ .separator ::
            List.replicate (occurrencePolarityFlag priorLiteral).toNat .tick ++ .separator ::
              List.replicate priorClause .tick ++ .separator ::
                List.replicate priorVertex .tick ++ tail) upper 0 0)
        (some (compatibilityEdgesCfg .taggedRestoreVertex buffer₁ finalBuffer₂
          test input output
          (List.replicate priorVertex .tick ++ .separator ::
            List.replicate priorClause .tick ++ .separator ::
              List.replicate (occurrencePolarityFlag priorLiteral).toNat .tick ++ .separator ::
                List.replicate (occurrenceVariableCode priorLiteral) .tick ++
                  .separator :: .frameEnd :: rowFlag :: work₁)
          tail upper 0 0))
        ((occurrenceVariableCode priorLiteral + 1) +
          ((occurrencePolarityFlag priorLiteral).toNat + 1) +
          (priorClause + 1) + 2 * priorVertex) := by
  rcases compatibilityEdges_restoreTaggedRowFieldTailRun priorClause priorVertex
    priorLiteral rowFlag input work₁ tail output buffer₁ test upper with
    ⟨finalBuffer₂, tailRun⟩
  refine ⟨finalBuffer₂, ?_⟩
  let full := EvalsToInTime.trans (step compatibilityEdgesProgram) _ _ _ _ _
    (compatibilityEdges_restoreTaggedRowFieldHeadRun priorClause priorVertex
      priorLiteral rowFlag input work₁ tail output buffer₁ test upper)
    tailRun
  convert full using 1 <;>
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end TMClique
end Turing
end Chapter34
end CLRS



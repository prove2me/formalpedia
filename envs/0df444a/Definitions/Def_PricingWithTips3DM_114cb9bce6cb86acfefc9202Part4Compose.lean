-- Prove2me | Definitions.Def_PricingWithTips3DM_114cb9bce6cb86acfefc9202Part4Compose
-- name    : PricingWithTips3DM_114cb9bce6cb86acfefc9202Part4Compose
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T00:30:53.652266+00:00
-- url     : https://prove2.me/theorems/d2d63d80-fc5c-457a-bd82-d81e2750161b
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesRestoreRow.Part4.Compose
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_114cb9bce6cb86acfefc9202Part4Fields
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition
namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique
open PolyBuilder

def compatibilityEdges_restoreTaggedRowComposedRun
    (priorClause priorPosition priorVertex : Nat) (priorLiteral : Literal)
    (compatible : Bool) (input work₁ tail : List UnaryFrameSym)
    (output : List CliqueSym) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) (upper : Nat) :
    Σ finalBuffer₂ : Option UnaryFrameSym,
      EvalsToInTime (step compatibilityEdgesProgram)
        (compatibilityEdgesCfg .taggedRestoreFlag buffer₁ buffer₂ test input output
          work₁ ((if compatible then .tick else .frameEnd) ::
            (encodeIndexedOccurrenceEntry
              (⟨⟨priorClause, priorPosition, priorLiteral⟩, priorVertex⟩)).reverse ++ tail)
          upper 0 0)
        (some (compatibilityEdgesCfg .taggedRestoreVertex buffer₁ finalBuffer₂
          test input output
          (List.replicate priorVertex .tick ++ .separator ::
            List.replicate priorClause .tick ++ .separator ::
              List.replicate (occurrencePolarityFlag priorLiteral).toNat .tick ++ .separator ::
                List.replicate (occurrenceVariableCode priorLiteral) .tick ++
                  .separator :: .frameEnd ::
                    (if compatible then .tick else .separator) :: work₁)
          tail upper 0 0))
        (((occurrenceVariableCode priorLiteral + 1) +
          ((occurrencePolarityFlag priorLiteral).toNat + 1) +
          (priorClause + 1) + 2 * priorVertex) + 4) := by
  rcases compatibilityEdges_restoreTaggedRowFieldsRun priorClause priorVertex
    priorLiteral (if compatible then .tick else .separator) input work₁ tail
    output buffer₁ test upper with ⟨finalBuffer₂, fields⟩
  refine ⟨finalBuffer₂, ?_⟩
  exact EvalsToInTime.trans (step compatibilityEdgesProgram) 4 _ _ _ _
    (compatibilityEdges_restoreTaggedRowPrefixRun
      priorClause priorPosition priorVertex priorLiteral compatible input work₁ tail
      output buffer₁ buffer₂ test upper)
    fields

end TMClique
end Turing
end Chapter34
end CLRS



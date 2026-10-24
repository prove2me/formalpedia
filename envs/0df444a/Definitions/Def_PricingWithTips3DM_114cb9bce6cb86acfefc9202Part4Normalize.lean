-- Prove2me | Definitions.Def_PricingWithTips3DM_114cb9bce6cb86acfefc9202Part4Normalize
-- name    : PricingWithTips3DM_114cb9bce6cb86acfefc9202Part4Normalize
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T00:34:49.398023+00:00
-- url     : https://prove2.me/theorems/7c63a728-fb97-4e6f-b043-b270158afd6d
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesRestoreRow.Part4.Normalize
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_114cb9bce6cb86acfefc9202Part4Compose
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition
namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique
open PolyBuilder

theorem compatibilityEdges_restoreTaggedRow_work_eq
    (priorClause priorPosition priorVertex : Nat) (priorLiteral : Literal)
    (compatible : Bool) (work₁ : List UnaryFrameSym) :
    List.replicate priorVertex .tick ++ .separator ::
      List.replicate priorClause .tick ++ .separator ::
        List.replicate (occurrencePolarityFlag priorLiteral).toNat .tick ++ .separator ::
          List.replicate (occurrenceVariableCode priorLiteral) .tick ++
            .separator :: .frameEnd ::
              (if compatible then .tick else .separator) :: work₁ =
      encodeIndexedOccurrenceEntry
          (⟨⟨priorClause, priorPosition, priorLiteral⟩, priorVertex⟩) ++
        [if compatible then .tick else .separator] ++ work₁ := by
  simp [encodeIndexedOccurrenceEntry, indexedOccurrenceRowValues,
    encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc]

theorem compatibilityEdges_restoreTaggedRow_steps_eq
    (priorClause priorPosition priorVertex : Nat) (priorLiteral : Literal) :
    ((occurrenceVariableCode priorLiteral + 1) +
      ((occurrencePolarityFlag priorLiteral).toNat + 1) +
      (priorClause + 1) + 2 * priorVertex) + 4 =
      compatibilityEdgesRestoreTaggedRowSteps
        (⟨⟨priorClause, priorPosition, priorLiteral⟩, priorVertex⟩) := by
  simp [compatibilityEdgesRestoreTaggedRowSteps, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm]
  omega

end TMClique
end Turing
end Chapter34
end CLRS



-- Prove2me | Definitions.Def_PricingWithTips3DM_114cb9bce6cb86acfefc9202Part4
-- name    : PricingWithTips3DM_114cb9bce6cb86acfefc9202Part4
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T00:35:58.464308+00:00
-- url     : https://prove2.me/theorems/e7a512ee-15f4-4d88-b790-f2877b0c3aa1
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesRestoreRow.Part4
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_114cb9bce6cb86acfefc9202Part4Normalize
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition
namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique
open PolyBuilder

/-- Exact local run from a previously consumed tag marker through one reversed
row.  The row is restored in forward order above work one, followed by its
one-symbol compatibility flag. -/
def compatibilityEdges_restoreTaggedRowRun
    (prior : IndexedOccurrence × Nat) (compatible : Bool)
    (input work₁ tail : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool) (upper : Nat) :
    Σ finalBuffer₂ : Option UnaryFrameSym,
      EvalsToInTime (step compatibilityEdgesProgram)
        (compatibilityEdgesCfg .taggedRestoreFlag buffer₁ buffer₂ test
          input output work₁
          ((if compatible then .tick else .frameEnd) ::
            (encodeIndexedOccurrenceEntry prior).reverse ++ tail) upper 0 0)
        (some (compatibilityEdgesCfg .taggedRestoreVertex buffer₁ finalBuffer₂
          test input output
          (encodeIndexedOccurrenceEntry prior ++
            [if compatible then .tick else .separator] ++ work₁)
          tail upper 0 0))
        (compatibilityEdgesRestoreTaggedRowSteps prior) := by
  rcases prior with ⟨priorOccurrence, priorVertex⟩
  rcases priorOccurrence with ⟨priorClause, priorPosition, priorLiteral⟩
  rcases compatibilityEdges_restoreTaggedRowComposedRun priorClause priorPosition
    priorVertex priorLiteral compatible input work₁ tail output buffer₁ buffer₂
    test upper with ⟨finalBuffer₂, run⟩
  refine ⟨finalBuffer₂, ?_⟩
  rw [compatibilityEdges_restoreTaggedRow_work_eq priorClause priorPosition
    priorVertex priorLiteral compatible work₁] at run
  rw [compatibilityEdges_restoreTaggedRow_steps_eq priorClause priorPosition
    priorVertex priorLiteral] at run
  exact run

end TMClique
end Turing
end Chapter34
end CLRS



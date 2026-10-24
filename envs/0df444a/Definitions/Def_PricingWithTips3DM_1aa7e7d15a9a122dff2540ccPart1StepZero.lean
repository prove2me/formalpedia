-- Prove2me | Definitions.Def_PricingWithTips3DM_1aa7e7d15a9a122dff2540ccPart1StepZero
-- name    : PricingWithTips3DM_1aa7e7d15a9a122dff2540ccPart1StepZero
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T01:44:29.42965+00:00
-- url     : https://prove2.me/theorems/f2e2e060-264b-47ea-8246-e6ed67f5a01e
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesEmitEdge.Part1.Step.zero
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_1aa7e7d15a9a122dff2540ccPart1Basic
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition
namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique
open PolyBuilder

def compatibilityEdges_copyCounterZeroRun
    (counter : CompatibilityEdgeCounter) (saved other : Nat)
    (input work₁ work₂ : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgeCounterCfg counter (compatibilityEdgeCopyLabel counter)
        buffer₁ buffer₂ test input output work₁ work₂ 0 other saved)
      (some (compatibilityEdgeCounterCfg counter
        (compatibilityEdgeRestoreLabel counter) buffer₁ buffer₂ false
        input output work₁ work₂ 0 other saved)) 1 := by
  cases counter <;> exact ⟨⟨1, by
    simp [flip, compatibilityEdgeCounterCfg, compatibilityEdgeCopyLabel,
      compatibilityEdgeRestoreLabel, step, compatibilityEdgesProgram,
      compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
end TMClique
end Turing
end Chapter34
end CLRS



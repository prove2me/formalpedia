-- Prove2me | Definitions.Def_PricingWithTips3DM_1aa7e7d15a9a122dff2540ccPart1Extend
-- name    : PricingWithTips3DM_1aa7e7d15a9a122dff2540ccPart1Extend
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T02:01:18.38991+00:00
-- url     : https://prove2.me/theorems/2cb84ee8-58f5-4294-9bd2-d9aa481dad0e
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesEmitEdge.Part1.Extend
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_1aa7e7d15a9a122dff2540ccPart1Step
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition
namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique
open PolyBuilder

def compatibilityEdges_copyCounterExtendRun
    (counter : CompatibilityEdgeCounter) (remaining saved other : Nat)
    (input work₁ work₂ : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (rest : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgeCounterCfg counter (compatibilityEdgeCopyLabel counter)
        buffer₁ buffer₂ true input (.tick :: output) work₁ work₂
        remaining other (saved + 1))
      (some (compatibilityEdgeCounterCfg counter
        (compatibilityEdgeRestoreLabel counter) buffer₁ buffer₂ false input
        (List.replicate remaining .tick ++ .tick :: output) work₁ work₂
        0 other ((saved + 1) + remaining))) (3 * remaining + 1)) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgeCounterCfg counter (compatibilityEdgeCopyLabel counter)
        buffer₁ buffer₂ test input output work₁ work₂
        (remaining + 1) other saved)
      (some (compatibilityEdgeCounterCfg counter
        (compatibilityEdgeRestoreLabel counter) buffer₁ buffer₂ false input
        (List.replicate (remaining + 1) .tick ++ output) work₁ work₂
        0 other (saved + (remaining + 1)))) (3 * (remaining + 1) + 1) := by
  let afterTick := compatibilityEdgeCounterCfg counter
    (compatibilityEdgeCopyLabel counter) buffer₁ buffer₂ true input
    (.tick :: output) work₁ work₂ remaining other (saved + 1)
  let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
    3 (3 * remaining + 1) _ afterTick _
      (by simpa [afterTick] using
        (compatibilityEdges_copyCounterTickRun counter remaining saved other
          input work₁ work₂ output buffer₁ buffer₂ test))
      rest
  convert full using 1 <;> try omega
  simp only [replicate_clique_tick_append_tick, Nat.add_comm, Nat.add_left_comm]

end TMClique
end Turing
end Chapter34
end CLRS



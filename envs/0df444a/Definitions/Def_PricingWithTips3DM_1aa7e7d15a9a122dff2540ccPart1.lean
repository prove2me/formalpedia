-- Prove2me | Definitions.Def_PricingWithTips3DM_1aa7e7d15a9a122dff2540ccPart1
-- name    : PricingWithTips3DM_1aa7e7d15a9a122dff2540ccPart1
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T02:03:04.848264+00:00
-- url     : https://prove2.me/theorems/0f6d55df-53b8-4d32-a48a-8b353b66170a
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesEmitEdge.Part1
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_1aa7e7d15a9a122dff2540ccPart1Extend
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

def compatibilityEdges_copyCounterRun
    (counter : CompatibilityEdgeCounter) (remaining saved : Nat)
    (input work₁ work₂ : List UnaryFrameSym)
    (output : List CliqueSym) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) (other : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgeCounterCfg counter (compatibilityEdgeCopyLabel counter)
        buffer₁ buffer₂ test input output work₁ work₂
        remaining other saved)
      (some (compatibilityEdgeCounterCfg counter
        (compatibilityEdgeRestoreLabel counter) buffer₁ buffer₂ false
        input (List.replicate remaining .tick ++ output) work₁ work₂
        0 other (saved + remaining))) (3 * remaining + 1) := by
  induction remaining generalizing saved test output with
  | zero =>
      simpa using compatibilityEdges_copyCounterZeroRun counter saved other
        input work₁ work₂ output buffer₁ buffer₂ test
  | succ remaining ih =>
      have rest := ih (saved := saved + 1) (test := true)
        (output := .tick :: output)
      exact compatibilityEdges_copyCounterExtendRun counter remaining saved other
        input work₁ work₂ output buffer₁ buffer₂ test rest
end TMClique
end Turing
end Chapter34
end CLRS



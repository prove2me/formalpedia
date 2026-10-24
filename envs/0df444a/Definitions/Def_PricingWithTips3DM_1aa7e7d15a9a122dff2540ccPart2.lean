-- Prove2me | Definitions.Def_PricingWithTips3DM_1aa7e7d15a9a122dff2540ccPart2
-- name    : PricingWithTips3DM_1aa7e7d15a9a122dff2540ccPart2
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T02:06:13.149269+00:00
-- url     : https://prove2.me/theorems/388602ef-a52d-4b7d-a527-e1764144e65b
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesEmitEdge.Part2
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_1aa7e7d15a9a122dff2540ccPart1
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

def compatibilityEdges_restoreCounterRun
    (counter : CompatibilityEdgeCounter) (saved restored : Nat)
    (input work₁ work₂ : List UnaryFrameSym)
    (output : List CliqueSym) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) (other : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgeCounterCfg counter
        (compatibilityEdgeRestoreLabel counter) buffer₁ buffer₂ test input
        output work₁ work₂ restored other saved)
      (some (compatibilityEdgeCounterCfg counter
        (compatibilityEdgeAfterRestoreLabel counter) buffer₁ buffer₂ false
        input output work₁ work₂ (restored + saved) other 0))
      (2 * saved + 1) := by
  induction saved generalizing restored test with
  | zero =>
      cases counter <;>
        exact ⟨⟨1, by
          simp [flip, compatibilityEdgeCounterCfg,
            compatibilityEdgeRestoreLabel, compatibilityEdgeAfterRestoreLabel,
            step, compatibilityEdgesProgram, compatibilityEdgesCfg, stepOp]⟩,
          le_rfl⟩
  | succ saved ih =>
      let afterIncrement := compatibilityEdgeCounterCfg counter
        (compatibilityEdgeRestoreLabel counter) buffer₁ buffer₂ true input
        output work₁ work₂ (restored + 1) other saved
      have first : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgeCounterCfg counter
            (compatibilityEdgeRestoreLabel counter) buffer₁ buffer₂ test input
            output work₁ work₂ restored other (saved + 1))
          (some afterIncrement) 2 := by
        cases counter <;>
          exact ⟨⟨2, by
            simp [Function.iterate_succ_apply, flip, afterIncrement,
              compatibilityEdgeCounterCfg, compatibilityEdgeRestoreLabel,
              List.replicate_succ, step, compatibilityEdgesProgram,
              compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
      have rest := ih (restored := restored + 1) (test := true)
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        2 (2 * saved + 1) _ afterIncrement _ first rest
      convert full using 1 <;> try omega
      simp only [Nat.add_comm, Nat.add_left_comm]

/-- Exact budget for writing one compatible normalized edge. -/
def compatibilityEdgesEmitCompatibleEdgeSteps (upper lower : Nat) : Nat :=
  5 * upper + 5 * lower + 7
end TMClique
end Turing
end Chapter34
end CLRS



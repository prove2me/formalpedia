-- Prove2me | Definitions.Def_PricingWithTips3DM_1aa7e7d15a9a122dff2540ccPart3
-- name    : PricingWithTips3DM_1aa7e7d15a9a122dff2540ccPart3
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T02:07:26.583231+00:00
-- url     : https://prove2.me/theorems/c6d42bfc-933c-4fe6-ac8e-85cf3f708505
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesEmitEdge.Part3
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_1aa7e7d15a9a122dff2540ccPart2
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- The compatible branch writes exactly the canonical normalized edge record
and restores both endpoint counters before entering lower cleanup. -/
def compatibilityEdges_emitCompatibleEdgeRun
    (upper lower : Nat) (input work₁ work₂ : List UnaryFrameSym)
    (output : List CliqueSym) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .pushEdgeEnd buffer₁ buffer₂ test input output
        work₁ work₂ upper lower 0)
      (some (compatibilityEdgesCfg .clearLower buffer₁ buffer₂ false input
        (encodeCliqueEdge (lower, upper) ++ output) work₁ work₂
        upper lower 0))
      (compatibilityEdgesEmitCompatibleEdgeSteps upper lower) := by
  have endRun : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .pushEdgeEnd buffer₁ buffer₂ test input output
        work₁ work₂ upper lower 0)
      (some (compatibilityEdgesCfg .copyUpper buffer₁ buffer₂ test input
        (.recordEnd :: output) work₁ work₂ upper lower 0)) 1 := by
    exact ⟨⟨1, by
      simp [flip, step, compatibilityEdgesProgram, compatibilityEdgesCfg,
        stepOp]⟩, le_rfl⟩
  have upperCopy := compatibilityEdges_copyCounterRun .upper upper 0 input
    work₁ work₂ (.recordEnd :: output) buffer₁ buffer₂ test lower
  have upperRestore := compatibilityEdges_restoreCounterRun .upper upper 0 input
    work₁ work₂
    (List.replicate upper .tick ++ .recordEnd :: output)
    buffer₁ buffer₂ false lower
  have pairRun : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .pushPairSeparator buffer₁ buffer₂ false input
        (List.replicate upper .tick ++ .recordEnd :: output)
        work₁ work₂ upper lower 0)
      (some (compatibilityEdgesCfg .copyLower buffer₁ buffer₂ false input
        (.pairSep :: List.replicate upper .tick ++ .recordEnd :: output)
        work₁ work₂ upper lower 0)) 1 := by
    exact ⟨⟨1, by
      simp [flip, step, compatibilityEdgesProgram, compatibilityEdgesCfg,
        stepOp]⟩, le_rfl⟩
  have lowerCopy := compatibilityEdges_copyCounterRun .lower lower 0 input
    work₁ work₂
    (.pairSep :: List.replicate upper .tick ++ .recordEnd :: output)
    buffer₁ buffer₂ false upper
  have lowerRestore := compatibilityEdges_restoreCounterRun .lower lower 0 input
    work₁ work₂
    (List.replicate lower .tick ++
      .pairSep :: List.replicate upper .tick ++ .recordEnd :: output)
    buffer₁ buffer₂ false upper
  have markRun : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .pushEdgeMark buffer₁ buffer₂ false input
        (List.replicate lower .tick ++
          .pairSep :: List.replicate upper .tick ++ .recordEnd :: output)
        work₁ work₂ upper lower 0)
      (some (compatibilityEdgesCfg .clearLower buffer₁ buffer₂ false input
        (.edgeMark :: List.replicate lower .tick ++
          .pairSep :: List.replicate upper .tick ++ .recordEnd :: output)
        work₁ work₂ upper lower 0)) 1 := by
    exact ⟨⟨1, by
      simp [flip, step, compatibilityEdgesProgram, compatibilityEdgesCfg,
        stepOp]⟩, le_rfl⟩
  let first := EvalsToInTime.trans (step compatibilityEdgesProgram)
    1 (3 * upper + 1) _ _ _ endRun (by
      simpa [compatibilityEdgeCounterCfg, compatibilityEdgeCopyLabel,
        compatibilityEdgeRestoreLabel] using upperCopy)
  let second := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ (2 * upper + 1) _ _ _ first (by
      simpa [compatibilityEdgeCounterCfg, compatibilityEdgeRestoreLabel,
        compatibilityEdgeAfterRestoreLabel] using upperRestore)
  let third := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ 1 _ _ _ second pairRun
  let fourth := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ (3 * lower + 1) _ _ _ third (by
      simpa [compatibilityEdgeCounterCfg, compatibilityEdgeCopyLabel,
        compatibilityEdgeRestoreLabel, List.append_assoc] using lowerCopy)
  let fifth := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ (2 * lower + 1) _ _ _ fourth (by
      simpa [compatibilityEdgeCounterCfg, compatibilityEdgeRestoreLabel,
        compatibilityEdgeAfterRestoreLabel, List.append_assoc] using lowerRestore)
  let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ 1 _ _ _ fifth (by simpa [List.append_assoc] using markRun)
  convert full using 1 <;>
    simp [encodeCliqueEdge, prependCliqueTicks_eq,
      compatibilityEdgesEmitCompatibleEdgeSteps, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]
  all_goals try omega
end TMClique
end Turing
end Chapter34
end CLRS



-- Prove2me | Definitions.Def_PricingWithTips3DM_114cb9bce6cb86acfefc9202Part3
-- name    : PricingWithTips3DM_114cb9bce6cb86acfefc9202Part3
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T23:36:00.176344+00:00
-- url     : https://prove2.me/theorems/d645054b-4d44-4b20-86de-25bc61c60c0b
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesRestoreRow.Part3
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_114cb9bce6cb86acfefc9202Part2
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

def compatibilityEdges_restoreVertexTicksRun
    (count : Nat) (input work₁ tail : List UnaryFrameSym)
    (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (upper : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .taggedRestoreVertex buffer₁ buffer₂ test
        input output work₁ (List.replicate count .tick ++ tail) upper 0 0)
      (some (compatibilityEdgesCfg .taggedRestoreVertex buffer₁
        (if count = 0 then buffer₂ else some .tick) test input output
        (List.replicate count .tick ++ work₁) tail upper 0 0))
      (2 * count) := by
  induction count generalizing buffer₂ work₁ with
  | zero =>
      exact ⟨⟨0, by simp⟩, le_rfl⟩
  | succ count ih =>
      let afterPush := compatibilityEdgesCfg .taggedRestoreVertex buffer₁
        (some .tick) test input output (.tick :: work₁)
        (List.replicate count .tick ++ tail) upper 0 0
      have first : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesCfg .taggedRestoreVertex buffer₁ buffer₂ test
            input output work₁
            (List.replicate (count + 1) .tick ++ tail) upper 0 0)
          (some afterPush) 2 := by
        exact ⟨⟨2, by
          simp [Function.iterate_succ_apply, flip, afterPush,
            List.replicate_succ, step, compatibilityEdgesProgram,
            compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
      have rest := ih (buffer₂ := some .tick) (work₁ := .tick :: work₁)
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        2 (2 * count) _ afterPush _ first rest
      convert full using 1 <;> try omega
      simp only [Nat.succ_ne_zero, if_false, ite_self,
        replicate_tick_append_tick]

/-- Exact budget for restoring one tagged occurrence row. -/
def compatibilityEdgesRestoreTaggedRowSteps
    (prior : IndexedOccurrence × Nat) : Nat :=
  2 * prior.2 + prior.1.clauseIndex +
    occurrencePolarityCode prior.1.literal +
    occurrenceVariableCode prior.1.literal + 7
end TMClique
end Turing
end Chapter34
end CLRS



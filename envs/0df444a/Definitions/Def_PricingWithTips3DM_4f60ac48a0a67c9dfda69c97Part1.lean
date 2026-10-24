-- Prove2me | Definitions.Def_PricingWithTips3DM_4f60ac48a0a67c9dfda69c97Part1
-- name    : PricingWithTips3DM_4f60ac48a0a67c9dfda69c97Part1
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T22:54:18.238893+00:00
-- url     : https://prove2.me/theorems/280934cc-bbf4-4df2-a5e1-94d9b7143d3a
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesCleanup.Part1
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_0e75ff46933231ddbfe3b079
import Mathlib.Tactic
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

def compatibilityEdges_clearClauseRun
    (clause : Nat) (input outputWork₁ work₂ : List UnaryFrameSym)
    (output : List CliqueSym) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) (upper variableCode : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .clearCurrentClause buffer₁ buffer₂ test
        input output outputWork₁ work₂ upper clause variableCode)
      (some (compatibilityEdgesCfg .clearCurrentVariable buffer₁ buffer₂
        false input output outputWork₁ work₂ upper 0 variableCode))
      (clause + 1) := by
  induction clause generalizing test with
  | zero =>
      exact ⟨⟨1, by
        simp [flip, step, compatibilityEdgesProgram, compatibilityEdgesCfg,
          stepOp]⟩, le_rfl⟩
  | succ clause ih =>
      let after := compatibilityEdgesCfg .clearCurrentClause buffer₁ buffer₂
        true input output outputWork₁ work₂ upper clause variableCode
      have first : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesCfg .clearCurrentClause buffer₁ buffer₂ test
            input output outputWork₁ work₂ upper (clause + 1)
            variableCode) (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, compatibilityEdgesProgram,
            compatibilityEdgesCfg, stepOp, List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (test := true)
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        1 (clause + 1) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm] using full
end TMClique
end Turing
end Chapter34
end CLRS



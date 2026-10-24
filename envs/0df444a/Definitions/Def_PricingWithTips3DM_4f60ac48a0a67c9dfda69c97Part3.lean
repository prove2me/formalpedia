-- Prove2me | Definitions.Def_PricingWithTips3DM_4f60ac48a0a67c9dfda69c97Part3
-- name    : PricingWithTips3DM_4f60ac48a0a67c9dfda69c97Part3
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T23:03:57.564308+00:00
-- url     : https://prove2.me/theorems/7a21ff3c-e7d8-4b34-9ae6-a1660aa7ff25
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesCleanup.Part3
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_4f60ac48a0a67c9dfda69c97Part2
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- Exact cleanup run from populated current-row counters to the tagged-row
restoration entry.  The upper endpoint remains available in counter one. -/
def compatibilityEdges_cleanupCurrentRun
    (upper clause variableCode : Nat)
    (input outputWork₁ work₂ : List UnaryFrameSym)
    (output : List CliqueSym) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .clearCurrentClause buffer₁ buffer₂ test
        input output outputWork₁ work₂ upper clause variableCode)
      (some (compatibilityEdgesCfg .taggedRestoreStart buffer₁ buffer₂
        false input output outputWork₁ work₂ upper 0 0))
      (clause + variableCode + 2) := by
  have first := compatibilityEdges_clearClauseRun clause input outputWork₁
    work₂ output buffer₁ buffer₂ test upper variableCode
  have rest := compatibilityEdges_clearVariableRun variableCode input
    outputWork₁ work₂ output buffer₁ buffer₂ false upper
  let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
    (clause + 1) (variableCode + 1) _ _ _ first rest
  convert full using 1 <;> omega
end TMClique
end Turing
end Chapter34
end CLRS



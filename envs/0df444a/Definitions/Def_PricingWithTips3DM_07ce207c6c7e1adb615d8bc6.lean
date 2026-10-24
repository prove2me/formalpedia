-- Prove2me | Definitions.Def_PricingWithTips3DM_07ce207c6c7e1adb615d8bc6
-- name    : PricingWithTips3DM_07ce207c6c7e1adb615d8bc6
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T21:04:39.709293+00:00
-- url     : https://prove2.me/theorems/15b39499-3b1b-48a1-ba4b-93e30b5db7b0
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.OccurrenceRowsTermination
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_7c842fc0a8e4823ad82f1884
import Mathlib.Tactic
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Indexed occurrence rows: termination

After the formula scan, both persistent counters are cleared and the builder
halts with no scratch data while retaining the exact reverse row stream.
-/

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

private theorem occurrenceRows_clearVertex_eval (vertex : Nat)
    (buffer : Option GraphSym) (test : Bool)
    (output : List UnaryFrameSym) (clause : Nat) :
    (flip Option.bind (step occurrenceRowsRevProgram))^[vertex + 1]
      (some (occurrenceRowsCfg .clearVertex buffer test [] output []
        vertex clause 0)) =
      some (occurrenceRowsCfg .clearClause buffer false [] output []
        0 clause 0) := by
  induction vertex generalizing test with
  | zero => rfl
  | succ vertex ih =>
      rw [show vertex + 1 + 1 = (vertex + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step occurrenceRowsRevProgram))^[vertex + 1]
          (some (occurrenceRowsCfg .clearVertex buffer true [] output []
            vertex clause 0)) = _
      exact ih true

private theorem occurrenceRows_clearClause_eval (clause : Nat)
    (buffer : Option GraphSym) (test : Bool)
    (output : List UnaryFrameSym) :
    (flip Option.bind (step occurrenceRowsRevProgram))^[clause + 1]
      (some (occurrenceRowsCfg .clearClause buffer test [] output []
        0 clause 0)) =
      some (occurrenceRowsCfg .halt buffer false [] output [] 0 0 0) := by
  induction clause generalizing test with
  | zero => rfl
  | succ clause ih =>
      rw [show clause + 1 + 1 = (clause + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step occurrenceRowsRevProgram))^[clause + 1]
          (some (occurrenceRowsCfg .clearClause buffer true [] output []
            0 clause 0)) = _
      exact ih true

/-- Exact full reverse-output cost on one semantic CNF. -/
def occurrenceRowsRevSteps (formula : CNF) : Nat :=
  occurrenceRowsFormulaSteps formula + cnfLiteralCount formula +
    occurrenceRowsFinalClause formula + 4

/-- The reverse-output builder reaches a fully cleared successful halt. -/
def occurrenceRowsRev_run (formula : CNF) :
    EvalsToInTime (step occurrenceRowsRevProgram)
      (initialCfg occurrenceRowsRevProgram (relabel (encCNF formula)))
      (some (haltCfg occurrenceRowsRevProgram
        (encodeIndexedOccurrenceRows formula).reverse))
      (occurrenceRowsRevSteps formula) := by
  rcases occurrenceRows_formulaRun formula with
    ⟨started, finalBuffer, finalTest, rows⟩
  let vertex := cnfLiteralCount formula
  let clause := occurrenceRowsFinalClause formula
  let reverseOutput := (encodeIndexedOccurrenceRows formula).reverse
  have scanEmpty : EvalsToInTime (step occurrenceRowsRevProgram)
      (occurrenceRowsCfg (.scan started) finalBuffer finalTest []
        reverseOutput [] vertex clause 0)
      (some (occurrenceRowsCfg .clearVertex none finalTest []
        reverseOutput [] vertex clause 0)) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have clearVertex : EvalsToInTime (step occurrenceRowsRevProgram)
      (occurrenceRowsCfg .clearVertex none finalTest []
        reverseOutput [] vertex clause 0)
      (some (occurrenceRowsCfg .clearClause none false []
        reverseOutput [] 0 clause 0)) (vertex + 1) :=
    ⟨⟨vertex + 1, occurrenceRows_clearVertex_eval vertex none finalTest
      reverseOutput clause⟩, le_rfl⟩
  have clearClause : EvalsToInTime (step occurrenceRowsRevProgram)
      (occurrenceRowsCfg .clearClause none false []
        reverseOutput [] 0 clause 0)
      (some (occurrenceRowsCfg .halt none false []
        reverseOutput [] 0 0 0)) (clause + 1) :=
    ⟨⟨clause + 1, occurrenceRows_clearClause_eval clause none false
      reverseOutput⟩, le_rfl⟩
  have halt : EvalsToInTime (step occurrenceRowsRevProgram)
      (occurrenceRowsCfg .halt none false [] reverseOutput [] 0 0 0)
      (some (haltCfg occurrenceRowsRevProgram reverseOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let h₁ := EvalsToInTime.trans (step occurrenceRowsRevProgram)
    (occurrenceRowsFormulaSteps formula) 1 _ _ _ rows scanEmpty
  let h₂ := EvalsToInTime.trans (step occurrenceRowsRevProgram)
    _ (vertex + 1) _ _ _ h₁ clearVertex
  let h₃ := EvalsToInTime.trans (step occurrenceRowsRevProgram)
    _ (clause + 1) _ _ _ h₂ clearClause
  let full := EvalsToInTime.trans (step occurrenceRowsRevProgram)
    _ 1 _ _ _ h₃ halt
  refine ⟨full.toEvalsTo, ?_⟩
  exact full.steps_le_m.trans (by
    simp [occurrenceRowsRevSteps, vertex, clause]
    omega)

end TMClique
end Turing
end Chapter34
end CLRS



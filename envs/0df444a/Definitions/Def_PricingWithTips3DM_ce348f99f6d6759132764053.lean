-- Prove2me | Definitions.Def_PricingWithTips3DM_ce348f99f6d6759132764053
-- name    : PricingWithTips3DM_ce348f99f6d6759132764053
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T21:58:39.757984+00:00
-- url     : https://prove2.me/theorems/0322daa3-d2db-410b-9695-f01815330658
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.BatchEdgeLookup.FinalCleanup
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_a342718b885ecefaa6fe4e65
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Batch edge lookup: final cleanup
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.BatchEdgeLookup

open PolyBuilder

/-- Discard the restored graph and traverse the empty cleanup stacks. -/
def discardGraph_run (answer : Bool) (input : List (Option CliqueSym))
    (output : List Bool)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.discardGraph answer) buffer₁ buffer₂ test input output [] [] [] [] [])
      (some (haltCfg program (answer :: output)))
      (input.length + 8) := by
  induction input generalizing buffer₁ with
  | nil =>
      exact ⟨⟨8, by
        simp [Function.iterate_succ_apply, flip, step, program, cfg, stepOp,
          haltCfg]⟩, le_rfl⟩
  | cons symbol input ih =>
      let after := cfg (.discardGraph answer) (some symbol) buffer₂ test input
        output [] [] [] [] []
      have first : EvalsToInTime (step program)
          (cfg (.discardGraph answer) buffer₁ buffer₂ test (symbol :: input)
            output [] [] [] [] [])
          (some after) 1 :=
        ⟨⟨1, by simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (buffer₁ := some symbol)
      let full := EvalsToInTime.trans (step program)
        1 (input.length + 8) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- Empty query work means the aggregate is final. -/
def final_run (answer : Bool) (input : List (Option CliqueSym))
    (output : List Bool)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.nextQuery answer) buffer₁ buffer₂ test input output [] [] [] [] [])
      (some (haltCfg program (answer :: output)))
      (input.length + 9) := by
  let after := cfg (.discardGraph answer) none buffer₂ test input output [] [] [] [] []
  have first : EvalsToInTime (step program)
      (cfg (.nextQuery answer) buffer₁ buffer₂ test input output [] [] [] [] [])
      (some after) 1 :=
    ⟨⟨1, by simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
  have rest := discardGraph_run answer input output none buffer₂ test
  let full := EvalsToInTime.trans (step program)
    1 (input.length + 8) _ after _ first rest
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.BatchEdgeLookup



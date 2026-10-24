-- Prove2me | Definitions.Def_PricingWithTips3DM_b89d42ff6c5843fa5b0cf05c
-- name    : PricingWithTips3DM_b89d42ff6c5843fa5b0cf05c
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:35:35.336981+00:00
-- url     : https://prove2.me/theorems/ef4b0741-2f2d-456f-b7f0-60db9bbaacaf
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OptionPairLeft.Run
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_9c7f8c7592c1658531af96f9
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Left pair formatter: exact reversed run
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder.OptionPairLeft

private def symbols_run {Γ : Type} [Fintype Γ]
    (input : List Γ) (output : List (Option Γ))
    (buffer₁ buffer₂ : Option Γ) (test : Bool) :
    EvalsToInTime (step (program Γ))
      (cfg Γ .scan buffer₁ buffer₂ test input output)
      (some (haltCfg (program Γ) ((format input).reverse ++ output)))
      (2 * input.length + 3) := by
  induction input generalizing output buffer₁ with
  | nil =>
      exact ⟨⟨3, by
        simp [Function.iterate_succ_apply, flip, format, step, program, cfg,
          stepOp, haltCfg]⟩, le_rfl⟩
  | cons symbol input ih =>
      let afterPop := cfg Γ (.emit symbol) (some symbol) buffer₂ test
        input output
      let afterEmit := cfg Γ .scan (some symbol) buffer₂ test
        input (some symbol :: output)
      have first : EvalsToInTime (step (program Γ))
          (cfg Γ .scan buffer₁ buffer₂ test (symbol :: input) output)
          (some afterPop) 1 :=
        ⟨⟨1, by simp [flip, afterPop, step, program, cfg, stepOp]⟩, le_rfl⟩
      have second : EvalsToInTime (step (program Γ)) afterPop
          (some afterEmit) 1 :=
        ⟨⟨1, by simp [flip, afterPop, afterEmit, step, program, cfg,
          stepOp]⟩, le_rfl⟩
      have rest := ih (output := some symbol :: output)
        (buffer₁ := some symbol)
      let firstTwo := EvalsToInTime.trans (step (program Γ))
        1 1 _ afterPop _ first second
      let full := EvalsToInTime.trans (step (program Γ))
        2 (2 * input.length + 3) _ afterEmit _ firstTwo rest
      simpa [format, List.reverse_append, List.reverse_cons,
        List.append_assoc, Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

/-- The direct controller emits the reverse of the pair-left format. -/
def run {Γ : Type} [Fintype Γ] (input : List Γ) :
    EvalsToInTime (step (program Γ))
      (initialCfg (program Γ) input)
      (some (haltCfg (program Γ) (format input).reverse))
      (2 * input.length + 3) := by
  simpa [initialCfg, cfg, program] using
    symbols_run input [] none none false

end CLRS.Chapter34.Turing.PolyBuilder.OptionPairLeft



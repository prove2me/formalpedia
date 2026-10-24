-- Prove2me | Definitions.Def_PricingWithTips3DM_12d2e8cf841ea25263d0c142
-- name    : PricingWithTips3DM_12d2e8cf841ea25263d0c142
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:27:42.7267+00:00
-- url     : https://prove2.me/theorems/407ff911-5b28-4b4c-9741-ba0d22a8fdcb
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialAffineUnaryProgression
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_118135686fa7e9d39e0f369b
import Definitions.Def_PricingWithTips3DM_12e60af373833ffa118e3422
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Exact polynomial affine unary progressions

This module connects raw source words to the runtime affine progression
controller.  A shared exact-polynomial compiler first emits the three unary
parameters {lit}`(base, step, count)`; the fixed affine controller then
expands them into every runtime value.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Evaluate three fixed natural polynomials into one runtime progression. -/
def exactPolynomialAffineUnaryProgression {Γ : Type}
    (base step count : Polynomial Nat) (input : List Γ) :
    AffineUnaryProgression :=
  { base := base.eval input.length
    step := step.eval input.length
    count := count.eval input.length }

/-- The structured progression encoding is byte-for-byte the existing exact
three-polynomial unary-frame family. -/
theorem exactPolynomialAffineUnaryProgression_encode {Γ : Type}
    (base step count : Polynomial Nat) (input : List Γ) :
    encodeAffineUnaryProgression
        (exactPolynomialAffineUnaryProgression base step count input) =
      exactPolynomialUnaryFrames [base, step, count] input := by
  rfl

/-- Public forward expansion from a raw source word. -/
def exactPolynomialAffineUnaryProgressionFrameStream {Γ : Type}
    (base step count : Polynomial Nat) (input : List Γ) :
    List UnaryFrameSym :=
  affineUnaryProgressionFrameStream
    (exactPolynomialAffineUnaryProgression base step count input)

set_option maxHeartbeats 800000 in
/-- A single fixed polynomial-time TM2 maps the raw source word to the exact
delimiter-bearing affine progression. -/
noncomputable def
    exactPolynomialAffineUnaryProgressionFrameStream_computableInPolyTime
    {Γ : Type} [Fintype Γ]
    (base step count : Polynomial Nat) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (@exactPolynomialAffineUnaryProgressionFrameStream
        Γ base step count) := by
  have source : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryProgression
      (@exactPolynomialAffineUnaryProgression Γ base step count) := by
    let compiled := exactPolynomialUnaryFrames_computableInPolyTime
      (Γ := Γ) [base, step, count]
    exact
      { tm := compiled.tm
        inputAlphabet := compiled.inputAlphabet
        outputAlphabet := compiled.outputAlphabet
        time := compiled.time
        outputsFun := fun input => by
          simpa [exactPolynomialAffineUnaryProgression_encode] using
            compiled.outputsFun input }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      source affineUnaryProgressionFrameStream_computableInPolyTime
  have hfunction :
      (fun input : List Γ =>
        affineUnaryProgressionFrameStream
          (exactPolynomialAffineUnaryProgression base step count input)) =
        @exactPolynomialAffineUnaryProgressionFrameStream
          Γ base step count := rfl
  rw [← hfunction]
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder



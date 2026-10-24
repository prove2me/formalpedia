-- Prove2me | Definitions.Def_PricingWithTips3DM_8596e3036db0561eca6c1166
-- name    : PricingWithTips3DM_8596e3036db0561eca6c1166
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:29:50.21439+00:00
-- url     : https://prove2.me/theorems/293a4904-35bd-4b6b-a5af-1de0cee61f98
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialUnaryFrameAffinePrefixRows
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_12e60af373833ffa118e3422
import Definitions.Def_PricingWithTips3DM_7084cfa7c9483f53f3e582be
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Exact-polynomial growing affine-prefix rows

This bridge evaluates two fixed natural polynomials into the runtime base and
row count consumed by the growing-prefix controller.  It packages the source
compiler and the controller as one reusable fixed polynomial-time TM2.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Evaluate two fixed natural polynomials into one growing-prefix family. -/
def exactPolynomialUnaryFrameAffinePrefixRows {Γ : Type}
    (base count : Polynomial Nat) (input : List Γ) :
    UnaryFrameAffinePrefixRows :=
  { base := base.eval input.length
    count := count.eval input.length }

/-- Its structured encoding is the exact two-polynomial unary-frame source. -/
theorem exactPolynomialUnaryFrameAffinePrefixRows_encode {Γ : Type}
    (base count : Polynomial Nat) (input : List Γ) :
    encodeUnaryFrameAffinePrefixRows
        (exactPolynomialUnaryFrameAffinePrefixRows base count input) =
      exactPolynomialUnaryFrames [base, count] input := by
  rfl

/-- Public marked-row stream obtained after evaluating the two parameters. -/
def exactPolynomialUnaryFrameAffinePrefixRowsStream {Γ : Type}
    (base count : Polynomial Nat) (input : List Γ) : List UnaryFrameSym :=
  unaryFrameAffinePrefixRowsStream
    (exactPolynomialUnaryFrameAffinePrefixRows base count input)

set_option maxHeartbeats 800000 in
/-- One fixed polynomial-time TM2 maps a raw word to all growing affine-prefix
rows determined by two fixed input-length polynomials. -/
noncomputable def
    exactPolynomialUnaryFrameAffinePrefixRowsStream_computableInPolyTime
    {Γ : Type} [Fintype Γ]
    (base count : Polynomial Nat) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (@exactPolynomialUnaryFrameAffinePrefixRowsStream Γ base count) := by
  have source : _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameAffinePrefixRows
      (@exactPolynomialUnaryFrameAffinePrefixRows Γ base count) := by
    let compiled := exactPolynomialUnaryFrames_computableInPolyTime
      (Γ := Γ) [base, count]
    exact
      { tm := compiled.tm
        inputAlphabet := compiled.inputAlphabet
        outputAlphabet := compiled.outputAlphabet
        time := compiled.time
        outputsFun := fun input => by
          simpa [exactPolynomialUnaryFrameAffinePrefixRows_encode] using
            compiled.outputsFun input }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source
      unaryFrameAffinePrefixRowsStream_computableInPolyTime
  have hfunction :
      (fun input : List Γ =>
        unaryFrameAffinePrefixRowsStream
          (exactPolynomialUnaryFrameAffinePrefixRows base count input)) =
        @exactPolynomialUnaryFrameAffinePrefixRowsStream
          Γ base count := rfl
  rw [← hfunction]
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder



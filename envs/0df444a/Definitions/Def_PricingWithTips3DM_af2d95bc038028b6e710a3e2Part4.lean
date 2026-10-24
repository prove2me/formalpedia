-- Prove2me | Definitions.Def_PricingWithTips3DM_af2d95bc038028b6e710a3e2Part4
-- name    : PricingWithTips3DM_af2d95bc038028b6e710a3e2Part4
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T23:28:41.605014+00:00
-- url     : https://prove2.me/theorems/759a2093-8d79-4c25-b49b-ca680966c4c9
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowInputCompiler.Part4
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_af2d95bc038028b6e710a3e2Part3
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-! ## Materialized halted and tail-prefix delimiters -/

/-- Semantic fixed values of one unified row.  The inserted zero is a real
unary field whose delimiter becomes the post-halted `frameEnd`. -/
noncomputable def arithmeticValidityRowFixedOperandValues
    (tm : _root_.Turing.FinTM2) (height start rowBase : Nat) : List Nat :=
  [ arithmeticHaltedMatchStart tm height start,
    rowBase,
    arithmeticNoneLabelWire tm rowBase,
    0 ] ++
    arithmeticValidityTailFixedOperandValues tm height start rowBase

theorem arithmeticValidityRowFixedOperandForms_eq_values
    (tm : _root_.Turing.FinTM2) (height start rowBase : Nat) :
    affineUnaryTripleMap (arithmeticValidityRowFixedOperandForms tm)
        (validityRowUnifiedAffineSeed height start rowBase) =
      arithmeticValidityRowFixedOperandValues
        tm height start rowBase := by
  exact arithmeticValidityRowFixedOperandForms_eq
    tm height start rowBase

/-- Fixed delimiter table: three ordinary halted operands, their explicit
boundary field, then the established complete tail-prefix table. -/
def arithmeticValidityRowFixedOperandDelimiters
    (tm : _root_.Turing.FinTM2) : List UnaryFrameSym :=
  [.separator, .separator, .separator, .frameEnd] ++
    arithmeticValidityTailFixedOperandDelimiters tm

@[simp] theorem arithmeticValidityRowFixedOperandDelimiters_nonempty
    (tm : _root_.Turing.FinTM2) :
    0 < (arithmeticValidityRowFixedOperandDelimiters tm).length := by
  simp [arithmeticValidityRowFixedOperandDelimiters]

/-- Every unified affine form has one verifier-fixed output delimiter. -/
theorem arithmeticValidityRowFixedOperandDelimiters_length
    (tm : _root_.Turing.FinTM2) :
    (arithmeticValidityRowFixedOperandDelimiters tm).length =
      (arithmeticValidityRowFixedOperandForms tm).length := by
  simp [arithmeticValidityRowFixedOperandDelimiters,
    arithmeticValidityRowFixedOperandForms,
    arithmeticValidityTailFixedOperandDelimiters_length]

theorem inputCompiler_encodeFixedDelimiters_append
    (left right : List Nat) (leftDelimiters rightDelimiters :
      List UnaryFrameSym)
    (hlength : left.length = leftDelimiters.length) :
    encodeUnaryFrameWithFixedDelimiters (left ++ right)
        (leftDelimiters ++ rightDelimiters) =
      encodeUnaryFrameWithFixedDelimiters left leftDelimiters ++
        encodeUnaryFrameWithFixedDelimiters right rightDelimiters := by
  induction left generalizing leftDelimiters with
  | nil =>
      cases leftDelimiters with
      | nil => rfl
      | cons delimiter delimiters => simp at hlength
  | cons value values ih =>
      cases leftDelimiters with
      | nil => simp at hlength
      | cons delimiter delimiters =>
          simp only [List.length_cons] at hlength
          have hlength' : values.length = delimiters.length :=
            Nat.add_right_cancel hlength
          simp [encodeUnaryFrameWithFixedDelimiters,
            ih delimiters hlength', List.append_assoc]

/-- Materializing the unified table preserves all three ordinary halted
separators, inserts their extra boundary, and then uses the established tail
delimiter table unchanged. -/
theorem arithmeticValidityRowFixedEncoding_eq
    (tm : _root_.Turing.FinTM2) (height start rowBase : Nat) :
    encodeUnaryFrameWithFixedDelimiters
        (arithmeticValidityRowFixedOperandValues
          tm height start rowBase)
        (arithmeticValidityRowFixedOperandDelimiters tm) =
      encodeUnaryFrame
          [ arithmeticHaltedMatchStart tm height start,
            rowBase,
            arithmeticNoneLabelWire tm rowBase ] ++
        [.frameEnd] ++
        encodeUnaryFrameWithFixedDelimiters
          (arithmeticValidityTailFixedOperandValues
            tm height start rowBase)
          (arithmeticValidityTailFixedOperandDelimiters tm) := by
  unfold arithmeticValidityRowFixedOperandValues
    arithmeticValidityRowFixedOperandDelimiters
  rw [inputCompiler_encodeFixedDelimiters_append]
  · simp [encodeUnaryFrameWithFixedDelimiters, encodeUnaryFrame,
      encodeUnaryFrameBlock, List.append_assoc]
  · rfl

theorem arithmeticValidityRowFixedOperandValues_length
    (tm : _root_.Turing.FinTM2) (height start rowBase : Nat) :
    (arithmeticValidityRowFixedOperandValues
        tm height start rowBase).length =
      (arithmeticValidityRowFixedOperandDelimiters tm).length := by
  have h := congrArg List.length
    (arithmeticValidityRowFixedOperandForms_eq_values
      tm height start rowBase)
  simpa [affineUnaryTripleMap,
    arithmeticValidityRowFixedOperandDelimiters_length] using h.symm

/-- The unified affine output is precisely a fixed-prefix splice input. -/
theorem verifierValidityRowUnifiedOperandPayloadFrames_eq_spliceInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowUnifiedOperandPayloadFrames W input =
      encodeUnaryFrameFixedPrefixSpliceInputFamily
        (fun seed : ValidityRowSeed =>
          arithmeticValidityRowFixedOperandValues W.machine.tm
            seed.height seed.start seed.rowBase)
        (fun seed : ValidityRowSeed =>
          encodeAffineExactlyOneCompactFamily
            (validityRowSeedOneHotFrames W.machine.tm seed))
        (verifierValidityRowSeeds W input) := by
  rw [verifierValidityRowUnifiedOperandPayloadFrames_eq_rows]
  generalize verifierValidityRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.flatMap_cons,
        encodeUnaryFrameFixedPrefixSpliceInputFamily]
      rw [show
        [ arithmeticHaltedMatchStart W.machine.tm seed.height seed.start,
          seed.rowBase,
          arithmeticNoneLabelWire W.machine.tm seed.rowBase,
          0 ] ++
            arithmeticValidityTailFixedOperandValues W.machine.tm
              seed.height seed.start seed.rowBase =
          arithmeticValidityRowFixedOperandValues W.machine.tm
            seed.height seed.start seed.rowBase by rfl]
      rw [ih]
end CLRS.Chapter34.Turing.CookLevin



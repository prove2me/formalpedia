-- Prove2me | Definitions.Def_PricingWithTips3DM_bbaac3743d036b03526ad1a7Part2Chunk7
-- name    : PricingWithTips3DM_bbaac3743d036b03526ad1a7Part2Chunk7
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T22:34:05.048902+00:00
-- url     : https://prove2.me/theorems/a541fbff-4fe7-447b-873c-3941997f0c48
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowTailSource.Part2.Chunk7
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_bbaac3743d036b03526ad1a7Part2Chunk6
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- The raw verifier word polynomially computes every row's fixed affine
operands while carrying the variable one-hot source invocations unchanged. -/
noncomputable def
    verifierValidityRowTailAffinePayloadFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowTailAffinePayloadFrames W) := by
  let normalizedSource :=
    verifierValidityRowSeedFirstOutputInvocationFrames_computableInPolyTime W
  let typedNormalizedSource :
      _root_.Turing.TM2ComputableInPolyTime id
        encodeAffineUnaryTriplePayloadFamily
        (verifierValidityRowTailPayloadFamily W) :=
    { tm := normalizedSource.tm
      inputAlphabet := normalizedSource.inputAlphabet
      outputAlphabet := normalizedSource.outputAlphabet
      time := normalizedSource.time
      outputsFun := fun input => by
        simpa only [id_eq,
          verifierValidityRowTailPayloadFamily_encoding_eq W input] using
          normalizedSource.outputsFun input }
  let affineSource := affineUnaryTriplePayloadFamily_computableInPolyTime
    (arithmeticValidityTailFixedOperandForms W.machine.tm)
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      typedNormalizedSource affineSource
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List Γ =>
      affineUnaryTriplePayloadRowOutputFamily
        (arithmeticValidityTailFixedOperandForms W.machine.tm)
        (verifierValidityRowTailPayloadRows W input))
  simpa [Function.comp_def, verifierValidityRowTailPayloadFamily] using
    Classical.choice composed

/-- The affine stage is exactly the generic fixed-prefix splice input: one
ordinary fixed table, an internal boundary, the protected one-hot payload,
and the outer row boundary. -/
theorem verifierValidityRowTailAffinePayloadFrames_eq_spliceInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowTailAffinePayloadFrames W input =
      encodeUnaryFrameFixedPrefixSpliceInputFamily
        (fun seed : ValidityRowSeed =>
          arithmeticValidityTailFixedOperandValues W.machine.tm
            seed.height seed.start seed.rowBase)
        (fun seed : ValidityRowSeed =>
          encodeAffineExactlyOneOutputSourceInvocationFamily
            (validityRowSeedOneHotFrames W.machine.tm seed).reverse)
        (verifierValidityRowSeeds W input) := by
  rw [verifierValidityRowTailAffinePayloadFrames_eq_rows]
  generalize verifierValidityRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.flatMap_cons,
        encodeUnaryFrameFixedPrefixSpliceInputFamily]
      rw [ih]
end CLRS.Chapter34.Turing.CookLevin



-- Prove2me | Definitions.Def_PricingWithTips3DM_bbaac3743d036b03526ad1a7Part2Chunk6
-- name    : PricingWithTips3DM_bbaac3743d036b03526ad1a7Part2Chunk6
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T22:28:30.655708+00:00
-- url     : https://prove2.me/theorems/b3ad489c-d3c7-4542-8640-2ae84065dca9
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowTailSource.Part2.Chunk6
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_bbaac3743d036b03526ad1a7Part2Chunk5
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Byte stream after the fixed affine table has been evaluated row by row;
the one-hot payload and both row boundaries are still present. -/
noncomputable def verifierValidityRowTailAffinePayloadFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  affineUnaryTriplePayloadRowOutputFamily
    (arithmeticValidityTailFixedOperandForms W.machine.tm)
    (verifierValidityRowTailPayloadRows W input)

/-- Exact row semantics of the payload-preserving affine stage. -/
theorem verifierValidityRowTailAffinePayloadFrames_eq_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowTailAffinePayloadFrames W input =
      (verifierValidityRowSeeds W input).flatMap fun seed =>
        encodeUnaryFrame
            (arithmeticValidityTailFixedOperandValues W.machine.tm
              seed.height seed.start seed.rowBase) ++
          [.frameEnd] ++
          encodeAffineExactlyOneOutputSourceInvocationFamily
              (validityRowSeedOneHotFrames W.machine.tm seed).reverse ++
            [.frameEnd] := by
  unfold verifierValidityRowTailAffinePayloadFrames
    verifierValidityRowTailPayloadRows
  generalize verifierValidityRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.map_cons, affineUnaryTriplePayloadRowOutputFamily,
        List.flatMap_cons]
      rw [ih]
      simp only [affineUnaryTriplePayloadRowOutput]
      rw [arithmeticValidityTailFixedOperandForms_eq]
end CLRS.Chapter34.Turing.CookLevin



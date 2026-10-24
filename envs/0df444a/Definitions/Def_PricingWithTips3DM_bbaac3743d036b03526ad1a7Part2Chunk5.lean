-- Prove2me | Definitions.Def_PricingWithTips3DM_bbaac3743d036b03526ad1a7Part2Chunk5
-- name    : PricingWithTips3DM_bbaac3743d036b03526ad1a7Part2Chunk5
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T22:25:03.132583+00:00
-- url     : https://prove2.me/theorems/47a80d3f-ced6-4766-b60f-418ec86fb86a
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowTailSource.Part2.Chunk5
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_bbaac3743d036b03526ad1a7Part2Chunk4
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- The normalized seed-first byte stream is definitionally the concrete
encoding of the typed payload family. -/
theorem verifierValidityRowTailPayloadFamily_encoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeAffineUnaryTriplePayloadFamily
        (verifierValidityRowTailPayloadFamily W input) =
      verifierValidityRowSeedFirstOutputInvocationFrames W input := by
  rw [verifierValidityRowSeedFirstOutputInvocationFrames_eq_rows]
  unfold encodeAffineUnaryTriplePayloadFamily
  change encodeAffineUnaryTriplePayloadRowFamily
      (verifierValidityRowTailPayloadRows W input) = _
  unfold verifierValidityRowTailPayloadRows
  generalize verifierValidityRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.map_cons, encodeAffineUnaryTriplePayloadRowFamily,
        List.flatMap_cons]
      rw [ih]
      simp [encodeAffineUnaryTriplePayloadRow,
        encodeAffineUnaryTripleSeed,
        encodeAffineExactlyOneStructuredRowSeed, validityRowAffineSeed,
        List.append_assoc]
end CLRS.Chapter34.Turing.CookLevin



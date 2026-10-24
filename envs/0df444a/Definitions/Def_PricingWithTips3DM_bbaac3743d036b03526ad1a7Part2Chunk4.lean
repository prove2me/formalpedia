-- Prove2me | Definitions.Def_PricingWithTips3DM_bbaac3743d036b03526ad1a7Part2Chunk4
-- name    : PricingWithTips3DM_bbaac3743d036b03526ad1a7Part2Chunk4
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T22:15:20.93289+00:00
-- url     : https://prove2.me/theorems/fa2312ae-a04c-4b0b-b534-5063a864c8df
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowTailSource.Part2.Chunk4
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_bbaac3743d036b03526ad1a7Part2Chunk3
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- One normalized verifier row, typed for the payload-preserving affine
source.  Its payload is exactly the compact one-hot source family already
computed by the seed-carrier normalization stage. -/
noncomputable def verifierValidityRowTailPayloadRows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List AffineUnaryTriplePayloadRow :=
  (verifierValidityRowSeeds W input).map fun seed =>
    { seed := validityRowAffineSeed seed.height seed.start seed.rowBase
      payload := encodeAffineExactlyOneOutputSourceInvocationFamily
        (validityRowSeedOneHotFrames W.machine.tm seed).reverse }

/-- Well-formed typed family presented to the generic affine source. -/
noncomputable def verifierValidityRowTailPayloadFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : AffineUnaryTriplePayloadFamily :=
  { rows := verifierValidityRowTailPayloadRows W input
    payload_frameEnd_free := by
      intro row hrow symbol hsymbol
      rw [verifierValidityRowTailPayloadRows, List.mem_map] at hrow
      rcases hrow with ⟨seed, hseed, rfl⟩
      exact affineExactlyOneOutputInvocationFamily_no_frameEnd _ symbol hsymbol }
end CLRS.Chapter34.Turing.CookLevin



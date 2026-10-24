-- Prove2me | Definitions.Def_PricingWithTips3DM_8c1e30c9d40f5a908d6541b8Part3
-- name    : PricingWithTips3DM_8c1e30c9d40f5a908d6541b8Part3
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T02:55:06.995737+00:00
-- url     : https://prove2.me/theorems/19c2eafa-65c9-49a3-b774-17d66900d349
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelMajorLabelChannels.Part3
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_8c1e30c9d40f5a908d6541b8Part2
import Definitions.Def_PricingWithTips3DM_7567c18233bee2ade1bb1d40
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

theorem
    verifierTransitionDispatchMuxInvocationLabelMajorTrueLabelFrames_eq_channel
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorTrueLabelFrames W input =
      verifierTransitionDispatchMuxInvocationDescriptorLabelPacketTrueFrames
        W input := by
  rw [
    verifierTransitionDispatchMuxInvocationLabelMajorTrueLabelFrames_eq_existing,
    ← verifierTransitionDispatchMuxInvocationDescriptorLabelPacketTrueFrames_eq]
end CLRS.Chapter34.Turing.CookLevin



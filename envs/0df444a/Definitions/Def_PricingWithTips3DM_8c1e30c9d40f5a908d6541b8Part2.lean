-- Prove2me | Definitions.Def_PricingWithTips3DM_8c1e30c9d40f5a908d6541b8Part2
-- name    : PricingWithTips3DM_8c1e30c9d40f5a908d6541b8Part2
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T02:51:24.658863+00:00
-- url     : https://prove2.me/theorems/ee06e3b9-56ea-4ac5-9c56-41e22216e795
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelMajorLabelChannels.Part2
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_8c1e30c9d40f5a908d6541b8Part1
import Definitions.Def_PricingWithTips3DM_f464f5b73553a5ce6a25fb85
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

theorem
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateLabelFrames_eq_channel
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateLabelFrames
        W input =
      verifierTransitionDispatchMuxInvocationDescriptorLabelPacketCoordinateFrames
        W input := by
  rw [
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateLabelFrames_eq_existing,
    ←
      verifierTransitionDispatchMuxInvocationDescriptorLabelPacketCoordinateFrames_eq]
end CLRS.Chapter34.Turing.CookLevin



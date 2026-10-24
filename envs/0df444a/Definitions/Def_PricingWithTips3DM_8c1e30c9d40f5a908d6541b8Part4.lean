-- Prove2me | Definitions.Def_PricingWithTips3DM_8c1e30c9d40f5a908d6541b8Part4
-- name    : PricingWithTips3DM_8c1e30c9d40f5a908d6541b8Part4
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T03:06:12.896139+00:00
-- url     : https://prove2.me/theorems/6f0ff0bf-bbb6-4836-8dc1-116cff542aa4
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelMajorLabelChannels.Part4
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_8c1e30c9d40f5a908d6541b8Part3
import Definitions.Def_PricingWithTips3DM_a1c02e7eaac6891e9c299d1d
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

theorem
    verifierTransitionDispatchMuxInvocationLabelMajorFalseLabelFrames_eq_channel
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorFalseLabelFrames W input =
      verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFalseFrames
        W input := by
  rw [
    verifierTransitionDispatchMuxInvocationLabelMajorFalseLabelFrames_eq_existing,
    ← verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFalseFrames_eq]
end CLRS.Chapter34.Turing.CookLevin



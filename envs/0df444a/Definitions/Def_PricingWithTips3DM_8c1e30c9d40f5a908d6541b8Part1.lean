-- Prove2me | Definitions.Def_PricingWithTips3DM_8c1e30c9d40f5a908d6541b8Part1
-- name    : PricingWithTips3DM_8c1e30c9d40f5a908d6541b8Part1
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T02:49:43.34399+00:00
-- url     : https://prove2.me/theorems/c5abe94a-a1a4-4980-a446-37b1d6801903
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelMajorLabelChannels.Part1
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_ed1da04e55c84fc3dcce3010
import Definitions.Def_PricingWithTips3DM_5fa2c8ddc93042763c0cb53c
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

theorem
    verifierTransitionDispatchMuxInvocationLabelMajorSelectorLabelFrames_eq_channel
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorSelectorLabelFrames
        W input =
      verifierTransitionDispatchMuxInvocationDescriptorLabelPacketSelectorFrames
        W input := by
  rw [
    verifierTransitionDispatchMuxInvocationLabelMajorSelectorLabelFrames_eq_existing,
    ←
      verifierTransitionDispatchMuxInvocationDescriptorLabelPacketSelectorFrames_eq]
end CLRS.Chapter34.Turing.CookLevin



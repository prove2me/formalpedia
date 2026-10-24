-- Prove2me | Definitions.Def_PricingWithTips3DM_8c1e30c9d40f5a908d6541b8Part5
-- name    : PricingWithTips3DM_8c1e30c9d40f5a908d6541b8Part5
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T03:11:25.628885+00:00
-- url     : https://prove2.me/theorems/876f9108-6271-4837-b151-93d0a805ae1f
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelMajorLabelChannels.Part5
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_8c1e30c9d40f5a908d6541b8Part4
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Machine-level evidence for the four independently executed label-major
channels.  A consumer must still provide a physical same-input fan-out and
row zipper before treating these witnesses as one packet compiler. -/
structure TransitionDispatchMuxInvocationLabelMajorChannelCompilers
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) where
  selector : _root_.Turing.TM2ComputableInPolyTime id id
    (verifierTransitionDispatchMuxInvocationLabelMajorSelectorLabelFrames W)
  coordinates : _root_.Turing.TM2ComputableInPolyTime id id
    (verifierTransitionDispatchMuxInvocationLabelMajorCoordinateLabelFrames W)
  whenTrue : _root_.Turing.TM2ComputableInPolyTime id id
    (verifierTransitionDispatchMuxInvocationLabelMajorTrueLabelFrames W)
  whenFalse : _root_.Turing.TM2ComputableInPolyTime id id
    (verifierTransitionDispatchMuxInvocationLabelMajorFalseLabelFrames W)

/-- The four concrete label-major pipelines satisfy the common compiler
interface. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorChannelCompilers
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    TransitionDispatchMuxInvocationLabelMajorChannelCompilers W :=
  { selector :=
      verifierTransitionDispatchMuxInvocationLabelMajorSelectorLabelFrames_computableInPolyTime
        W
    coordinates :=
      verifierTransitionDispatchMuxInvocationLabelMajorCoordinateLabelFrames_computableInPolyTime
        W
    whenTrue :=
      verifierTransitionDispatchMuxInvocationLabelMajorTrueLabelFrames_computableInPolyTime
        W
    whenFalse :=
      verifierTransitionDispatchMuxInvocationLabelMajorFalseLabelFrames_computableInPolyTime
        W }
end CLRS.Chapter34.Turing.CookLevin



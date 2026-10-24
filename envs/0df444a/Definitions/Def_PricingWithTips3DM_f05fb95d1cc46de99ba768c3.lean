-- Prove2me | Definitions.Def_PricingWithTips3DM_f05fb95d1cc46de99ba768c3
-- name    : PricingWithTips3DM_f05fb95d1cc46de99ba768c3
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T01:11:12.319982+00:00
-- url     : https://prove2.me/theorems/5df1998a-736b-42fd-b82e-4108c7e35d10
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelMajorMarkedDescriptorSemantics
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_ba14293054b2afac60164995
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Physical semantics of marked label-major dispatch descriptors

The source module supplies the concrete delimiter-rewriting TM2, while the
semantics module identifies its ordinary unary values with canonical
label-local descriptor packets.  This file joins those two interfaces: the
actual machine output is exactly the cyclic unary encoding of the canonical
descriptor values under the verifier-fixed label-boundary table.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Canonical physical target of the label-major delimiter pass. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorCanonicalMarkedDescriptorFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  encodeUnaryFrameWithDelimiterCycle
    (transitionDispatchMuxInvocationLabelMajorDescriptorDelimiterTable
      W.machine.tm)
    (transitionDispatchMuxInvocationLabelMajorDescriptorDelimiterTable_nonempty
      W.machine.tm)
    ((verifierTransitionRowSeeds W input).flatMap fun seed =>
      (transitionDispatchMuxInvocationLabelMajorCanonicalDescriptorValueGroups
        W.machine.tm seed).flatten)

/-- The concrete raw-input delimiter machine emits the canonical marked
descriptor value stream byte for byte. -/
theorem
    verifierTransitionDispatchMuxInvocationLabelMajorMarkedDescriptorFrames_eq_canonical
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorMarkedDescriptorFrames
        W input =
      verifierTransitionDispatchMuxInvocationLabelMajorCanonicalMarkedDescriptorFrames
        W input := by
  unfold
    verifierTransitionDispatchMuxInvocationLabelMajorMarkedDescriptorFrames
    verifierTransitionDispatchMuxInvocationLabelMajorCanonicalMarkedDescriptorFrames
  rw [
    verifierTransitionDispatchMuxInvocationLabelMajorDescriptorFrames_eq_canonical]
  exact rewriteUnaryFrameDelimiters_encodeUnaryFrame _ _ _

end CLRS.Chapter34.Turing.CookLevin



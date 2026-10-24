-- Prove2me | Definitions.Def_PricingWithTips3DM_35a7147734983807078575c9
-- name    : PricingWithTips3DM_35a7147734983807078575c9
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T01:53:35.485296+00:00
-- url     : https://prove2.me/theorems/9f77536f-0f26-4171-ae67-258e315a035a
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorLabelReassembly
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_07f3fdf8789b7e6fee3d53d4
import Definitions.Def_PricingWithTips3DM_52ebeffb5829f0970ee79999
import Definitions.Def_PricingWithTips3DM_a394b16d73df8713f1abc05c
import Definitions.Def_PricingWithTips3DM_8a1f10a645508152b1ccd338
import Definitions.Def_PricingWithTips3DM_e2485af017e759ca4f99350b
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Exact label-packet contract for dispatch-mux reassembly

The four descriptor interpreters now recover one selector, coordinate, true-
arm, and false-arm row per fixed program label.  This module fixes the exact
seed-major physical packet expected by the final streaming reassembler and
proves that the corresponding structured views expand byte-for-byte to the
already verified affine mux-invocation source.

No machine is hidden in this layer: the input packet and output source are
both explicit lists of `UnaryFrameSym`.  The later controller proof can
therefore concentrate solely on realizing this exact relation.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Four canonical marked rows carrying one dispatch label.  The order is
chosen to match the data dependencies of the final assembler: selector,
fresh coordinates, true arm, then false arm. -/
def TransitionDispatchMuxInvocationView.labelPacketFrames
    (view : TransitionDispatchMuxInvocationView) : List UnaryFrameSym :=
  encodeUnaryFrame [view.selector] ++ [.frameEnd] ++
    transitionDispatchMuxCoordinateRowFrames view.coordinates ++
    [.frameEnd] ++
    encodeUnaryFrame view.whenTrue ++ [.frameEnd] ++
    encodeUnaryFrame view.whenFalse ++ [.frameEnd]

/-- Exact affine-progression source contributed by one reconstructed label
view. -/
def TransitionDispatchMuxInvocationView.sourceFrames
    (view : TransitionDispatchMuxInvocationView) : List UnaryFrameSym :=
  view.invocationSegments.flatMap
    AffineMuxInvocationProgression.sourceFrames

/-- Source frames obtained by reassembling a list of aligned label views. -/
def transitionDispatchMuxInvocationViewsSourceFrames
    (views : List TransitionDispatchMuxInvocationView) :
    List UnaryFrameSym :=
  affineMuxInvocationProgressionFamilySourceFrames
    (views.flatMap TransitionDispatchMuxInvocationView.invocationSegments)

/-- Reassembly is compatible with label boundaries: the generic affine
source of the concatenated segment family is exactly the concatenation of
the source contributed by each label view. -/
theorem transitionDispatchMuxInvocationViewsSourceFrames_eq
    (views : List TransitionDispatchMuxInvocationView) :
    transitionDispatchMuxInvocationViewsSourceFrames views =
      views.flatMap TransitionDispatchMuxInvocationView.sourceFrames := by
  unfold transitionDispatchMuxInvocationViewsSourceFrames
    TransitionDispatchMuxInvocationView.sourceFrames
  rw [affineMuxInvocationProgressionFamilySourceFrames_eq]
  exact List.flatMap_assoc

/-- Seed-major physical input contract for the final label reassembler. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  (verifierTransitionRowSeeds W input).flatMap fun seed =>
    (transitionDispatchMuxDescriptorInvocationViews W.machine.tm seed).flatMap
      TransitionDispatchMuxInvocationView.labelPacketFrames

/-- Every field of the physical reassembly contract is the corresponding
field of the actual proof-carrying dispatch artifact. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFrames_eq_artifacts
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFrames
        W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        (transitionDispatchArtifactsFromSeed W.machine.tm seed).flatMap
          fun artifact => artifact.muxInvocationView.labelPacketFrames := by
  unfold
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFrames
  apply List.flatMap_congr
  intro seed hseed
  rw [transitionDispatchMuxDescriptorInvocationViews_eq_artifacts
    W input seed hseed]
  rw [List.flatMap_map]

/-- The output side of the label-packet contract is literally the canonical
source already consumed by the verified affine mux controller. -/
theorem
    verifierTransitionDispatchMuxDescriptorInvocationSourceFrames_eq_reassembledViews
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxDescriptorInvocationSourceFrames W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        (transitionDispatchMuxDescriptorInvocationViews W.machine.tm
          seed).flatMap
            TransitionDispatchMuxInvocationView.sourceFrames := by
  unfold verifierTransitionDispatchMuxDescriptorInvocationSourceFrames
    verifierTransitionDispatchMuxDescriptorInvocationSegments
  rw [affineMuxInvocationProgressionFamilySourceFrames_eq]
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro seed hseed
  unfold transitionDispatchMuxDescriptorInvocationSegments
    TransitionDispatchMuxInvocationView.sourceFrames
  exact List.flatMap_assoc

end CLRS.Chapter34.Turing.CookLevin



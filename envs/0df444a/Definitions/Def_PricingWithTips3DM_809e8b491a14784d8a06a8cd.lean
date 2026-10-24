-- Prove2me | Definitions.Def_PricingWithTips3DM_809e8b491a14784d8a06a8cd
-- name    : PricingWithTips3DM_809e8b491a14784d8a06a8cd
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T04:09:11.568513+00:00
-- url     : https://prove2.me/theorems/f55befa4-6883-4677-b06f-f945b61bfa42
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchQuotedMuxRows
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_70e949f1de7d8f9866352485
import Definitions.Def_PricingWithTips3DM_ea14fe4aa439d45b6affeebf
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Quoted rows for every outer dispatch mux

The already closed label-major packet compiler and mux expander are retargeted
to their typed invocation views, then composed with the delimiter-safe parser.
The output order is seed-major and label-minor, matching the canonical
dispatch artifact order.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Canonical global mux bytes are exactly the encoding of the reconstructed
seed-major typed views. -/
theorem verifierTransitionDispatchMuxInvocationFrames_eq_viewFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationFrames W input =
      transitionMuxInvocationViewFamilyFrames
        (verifierTransitionDispatchMuxInvocationViews W input) := by
  unfold verifierTransitionDispatchMuxInvocationFrames
    transitionMuxInvocationViewFamilyFrames
    verifierTransitionDispatchMuxInvocationViews
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro seed hseed
  rw [transitionDispatchMuxDescriptorInvocationViews_eq_artifacts W input
    seed hseed]
  rw [List.flatMap_map]
  exact
    (transitionDispatchArtifactsFromSeed_muxInvocationViews_encode
      W.machine.tm seed).symm

/-- The physical global mux machine exposed through its typed view family. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationViews_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      transitionMuxInvocationViewFamilyFrames
      (verifierTransitionDispatchMuxInvocationViews W) := by
  let raw :=
    verifierTransitionDispatchMuxInvocationFrames_computableInPolyTime_of_labelPacketCompiler
      W
      (verifierTransitionDispatchMuxInvocationLabelMajorPacketFamily_computableInPolyTime
        W)
  exact
    { tm := raw.tm
      inputAlphabet := raw.inputAlphabet
      outputAlphabet := raw.outputAlphabet
      time := raw.time
      outputsFun := fun input => by
        have run := raw.outputsFun input
        rw [verifierTransitionDispatchMuxInvocationFrames_eq_viewFamily W
          input] at run
        simpa only [id_eq] using run }

/-- Marked quoted rows for every outer dispatch mux invocation. -/
noncomputable def verifierTransitionDispatchQuotedMuxFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  transitionMuxInvocationQuotedRowFamily
    (verifierTransitionDispatchMuxInvocationViews W input)

@[simp] theorem verifierTransitionDispatchQuotedMuxFamily_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierTransitionDispatchQuotedMuxFamily W input).rows =
      (verifierTransitionDispatchMuxInvocationViews W input).map fun view =>
        quoteUnaryFrameStream view.encode := rfl

/-- Concrete raw-input compiler for all quoted outer mux rows. -/
noncomputable def
    verifierTransitionDispatchQuotedMuxFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierTransitionDispatchQuotedMuxFamily W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationViews_computableInPolyTime W)
      transitionMuxQuotedRowParser_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id
    encodeUnaryFrameMarkedRowFamily
    (fun input => transitionMuxInvocationQuotedRowFamily
      (verifierTransitionDispatchMuxInvocationViews W input))
  simpa only [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin



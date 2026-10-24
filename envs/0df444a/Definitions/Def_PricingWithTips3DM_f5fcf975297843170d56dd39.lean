-- Prove2me | Definitions.Def_PricingWithTips3DM_f5fcf975297843170d56dd39
-- name    : PricingWithTips3DM_f5fcf975297843170d56dd39
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T00:55:33.304198+00:00
-- url     : https://prove2.me/theorems/ca7be51d-276e-425b-ad9d-c539d75c4236
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorPacketNormalize
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_b7a225dc54c0d9001cbf0224
import Definitions.Def_PricingWithTips3DM_727ce292d041978990457202
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Standard marked-row normalization of duplicated mux packets

The unified descriptor packets now exist twice on the physical output tape.
This module restores the ordinary delimiter of each packet's last unary field,
making both copies valid inputs for the established marked-row prefix/suffix
routing controllers.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Standard marked-row representation of both descriptor packet copies. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorStandardDuplicatedPacketFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  restoreUnaryFrameFixedWidthPacketSeparators
    (verifierTransitionDispatchMuxInvocationDescriptorDuplicatedPacketFrames
      W input)

/-- Both physical copies are exact ordinary unary rows with retained final
field separators and outer row markers. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorStandardDuplicatedPacketFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorStandardDuplicatedPacketFrames
        W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        let row := encodeUnaryFrame
          (transitionDispatchMuxInvocationDescriptorValues W.machine.tm seed) ++
          [.frameEnd]
        row ++ row := by
  unfold
    verifierTransitionDispatchMuxInvocationDescriptorStandardDuplicatedPacketFrames
    restoreUnaryFrameFixedWidthPacketSeparators
  rw [verifierTransitionDispatchMuxInvocationDescriptorDuplicatedPacketFrames_eq]
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro seed hseed
  simp only [List.flatMap_append]
  have hne :
      transitionDispatchMuxInvocationDescriptorValues W.machine.tm seed ≠
        [] := by
    intro hempty
    have hlength :=
      transitionDispatchMuxInvocationDescriptorValues_length
        W.machine.tm seed
    rw [hempty] at hlength
    simp only [List.length_nil] at hlength
    have hpositive :=
      transitionDispatchMuxInvocationDescriptorPacketWidth_pos W.machine.tm
    omega
  cases hvalues :
      transitionDispatchMuxInvocationDescriptorValues W.machine.tm seed with
  | nil => exact False.elim (hne hvalues)
  | cons value values =>
      have hone :=
        restoreUnaryFrameFixedWidthPacketSeparators_encode value values
      unfold restoreUnaryFrameFixedWidthPacketSeparators at hone
      simpa only [hvalues] using congrArg (fun frames => frames ++ frames) hone

/-- Packet marking, duplication, and canonical row normalization form one
continuous polynomial-time source pipeline from the verifier word. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorStandardDuplicatedPacketFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorStandardDuplicatedPacketFrames
        W) := by
  let duplicated :=
    verifierTransitionDispatchMuxInvocationDescriptorDuplicatedPacketFrames_computableInPolyTime
      W
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      duplicated
      restoreUnaryFrameFixedWidthPacketSeparators_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List Γ =>
      restoreUnaryFrameFixedWidthPacketSeparators
        (verifierTransitionDispatchMuxInvocationDescriptorDuplicatedPacketFrames
          W input))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin



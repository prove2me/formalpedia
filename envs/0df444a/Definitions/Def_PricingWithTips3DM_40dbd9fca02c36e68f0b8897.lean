-- Prove2me | Definitions.Def_PricingWithTips3DM_40dbd9fca02c36e68f0b8897
-- name    : PricingWithTips3DM_40dbd9fca02c36e68f0b8897
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T02:22:17.989017+00:00
-- url     : https://prove2.me/theorems/badac2a4-4f71-4f1e-9e1a-de756b029e71
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelMajorFalseFrames
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_d31d920ac0b45f37a1290211
import Definitions.Def_PricingWithTips3DM_47a1c02df493e71357c55f3c
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# False-arm descriptors from label-major dispatch packets

The fourth row of each physical packet stores the label-local false-arm
progression family.  A fixed periodic selector recovers those marked rows;
erasing their markers produces exactly the canonical adjacent seven-field
false descriptor family consumed by the established interpreter.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

private theorem
    transitionDispatchMuxInvocationLabelMajorDescriptorPacketsFrom_falseProgressions
    (tm : _root_.Turing.FinTM2)
    (selectors : List Nat)
    (coordinateGroups : List (List AffineUnaryTripleProgression))
    (trueLayouts : List (TransitionDispatchTrueArmNormalizedLayout tm))
    (falseGroups : List (List AffineUnaryTripleProgression))
    (hcoordinate : coordinateGroups.length = selectors.length)
    (htrue : trueLayouts.length = selectors.length)
    (hfalse : falseGroups.length = selectors.length) :
    (transitionDispatchMuxInvocationLabelMajorDescriptorPacketsFrom tm
        selectors coordinateGroups trueLayouts falseGroups).map
        (fun packet => packet.falseProgressions) = falseGroups := by
  induction selectors generalizing coordinateGroups trueLayouts falseGroups with
  | nil =>
      simp only [List.length_nil] at hfalse
      have hfalseNil : falseGroups = [] := by simpa using hfalse
      subst falseGroups
      rfl
  | cons selector selectors ih =>
      cases coordinateGroups with
      | nil => simp at hcoordinate
      | cons coordinates coordinateGroups =>
          cases trueLayouts with
          | nil => simp at htrue
          | cons trueLayout trueLayouts =>
              cases falseGroups with
              | nil => simp at hfalse
              | cons whenFalse falseGroups =>
                  simp only [
                    transitionDispatchMuxInvocationLabelMajorDescriptorPacketsFrom,
                    List.map_cons]
                  congr 1
                  apply ih
                  · simpa using hcoordinate
                  · simpa using htrue
                  · simpa using hfalse

/-- Packet projection recovers the canonical false progression groups on
each verifier-produced transition seed. -/
theorem
    transitionDispatchMuxInvocationLabelMajorDescriptorPackets_falseProgressions
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input) :
    (transitionDispatchMuxInvocationLabelMajorDescriptorPackets
        W.machine.tm seed).map (fun packet => packet.falseProgressions) =
      transitionDispatchFalseArmProgressionGroups W.machine.tm seed := by
  unfold transitionDispatchMuxInvocationLabelMajorDescriptorPackets
  apply
    transitionDispatchMuxInvocationLabelMajorDescriptorPacketsFrom_falseProgressions
  · rw [transitionDispatchMuxCoordinateProgressionGroups_length,
      transitionDispatchSelectors_length]
  · have hlength :=
      transitionDispatchTrueArmSpanProgressionGroups_length W.machine.tm seed
    unfold transitionDispatchTrueArmSpanProgressionGroups at hlength
    simp only [List.length_map] at hlength
    rw [hlength, transitionDispatchSelectors_length]
  · rw [transitionDispatchFalseArmProgressionGroups_length W input seed hseed,
      transitionDispatchSelectors_length]

/-- Flattening the packet-local fourth fields yields the standard false-arm
progression family in seed-major order. -/
theorem verifierTransitionDispatchMuxInvocationLabelMajorFalseProgressions_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    ((verifierTransitionRowSeeds W input).flatMap fun seed =>
      (transitionDispatchMuxInvocationLabelMajorDescriptorPackets
        W.machine.tm seed).flatMap fun packet => packet.falseProgressions) =
      (verifierTransitionRowSeeds W input).flatMap
        (transitionDispatchFalseArmProgressions W.machine.tm) := by
  apply List.flatMap_congr
  intro seed hseed
  have hgroups :=
    transitionDispatchMuxInvocationLabelMajorDescriptorPackets_falseProgressions
      W input seed hseed
  have hflattened := congrArg List.flatten hgroups
  simpa [List.flatten_eq_flatMap, List.flatMap_map, Function.comp_def,
    transitionDispatchFalseArmProgressionGroups,
    transitionDispatchFalseArmProgressions] using hflattened

/-- Select the fourth row of each selector/coordinate/true/false packet. -/
def transitionDispatchMuxInvocationLabelMajorFalseSelection : List Bool :=
  [false, false, false, true]

theorem transitionDispatchMuxInvocationLabelMajorFalseSelection_nonempty :
    0 < transitionDispatchMuxInvocationLabelMajorFalseSelection.length := by
  simp [transitionDispatchMuxInvocationLabelMajorFalseSelection]

/-- Selected, still label-marked false descriptor rows. -/
noncomputable def verifierTransitionDispatchMuxInvocationLabelMajorFalseMarkedRows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFramePeriodicMarkedRows
    transitionDispatchMuxInvocationLabelMajorFalseSelection
    transitionDispatchMuxInvocationLabelMajorFalseSelection_nonempty
    (verifierTransitionDispatchMuxInvocationLabelMajorFourRowNormalizedFrames
      W input)

theorem verifierTransitionDispatchMuxInvocationLabelMajorFalseMarkedRows_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorFalseMarkedRows W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        (transitionDispatchMuxInvocationLabelMajorDescriptorPackets
          W.machine.tm seed).flatMap fun packet =>
            encodeUnaryFrame
                (transitionDispatchProgressionDescriptorValues
                  packet.falseProgressions) ++ [.frameEnd] := by
  unfold verifierTransitionDispatchMuxInvocationLabelMajorFalseMarkedRows
  rw [
    verifierTransitionDispatchMuxInvocationLabelMajorFourRowNormalizedFrames_eq]
  rw [rewriteUnaryFramePeriodicMarkedRows_encode]
  rw [encodeUnaryFramePeriodicMarkedRowOutput_groups _ _ _]
  · unfold
      verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroups
    rw [List.flatMap_assoc]
    apply List.flatMap_congr
    intro seed hseed
    rw [List.flatMap_map]
    apply List.flatMap_congr
    intro packet hpacket
    simp [transitionDispatchMuxInvocationLabelMajorFalseSelection,
      TransitionDispatchMuxInvocationLabelMajorDescriptorPacket.fourRowDescriptorValueGroups,
      encodeUnaryFramePeriodicSelectedMarkedRows]
  · intro group hgroup
    simpa [transitionDispatchMuxInvocationLabelMajorFalseSelection] using
      (verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroups_length
        W input group hgroup)

/-- Adjacent seven-field descriptor stream obtained from the new fourth-row
channel. -/
noncomputable def verifierTransitionDispatchMuxInvocationLabelMajorFalseFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  unmarkAffineUnaryTripleProgressionRows
    (verifierTransitionDispatchMuxInvocationLabelMajorFalseMarkedRows W input)

theorem verifierTransitionDispatchMuxInvocationLabelMajorFalseFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorFalseFrames W input =
      encodeAffineUnaryTripleProgressionFamily
        ((verifierTransitionRowSeeds W input).flatMap fun seed =>
          (transitionDispatchMuxInvocationLabelMajorDescriptorPackets
            W.machine.tm seed).flatMap fun packet =>
              packet.falseProgressions) := by
  unfold verifierTransitionDispatchMuxInvocationLabelMajorFalseFrames
  rw [verifierTransitionDispatchMuxInvocationLabelMajorFalseMarkedRows_eq]
  rw [show
      (verifierTransitionRowSeeds W input).flatMap
          (fun seed =>
            (transitionDispatchMuxInvocationLabelMajorDescriptorPackets
              W.machine.tm seed).flatMap fun packet =>
                encodeUnaryFrame
                    (transitionDispatchProgressionDescriptorValues
                      packet.falseProgressions) ++ [.frameEnd]) =
        (((verifierTransitionRowSeeds W input).flatMap fun seed =>
          (transitionDispatchMuxInvocationLabelMajorDescriptorPackets
            W.machine.tm seed).map fun packet =>
              transitionDispatchProgressionDescriptorValues
                packet.falseProgressions).flatMap fun row =>
                  encodeUnaryFrame row ++ [.frameEnd]) by
      simp [List.flatMap_assoc, List.flatMap_map]]
  rw [unmarkAffineUnaryTripleProgressionRows_markedValues]
  rw [encodeAffineUnaryTripleProgressionFamily_eq_encodeUnaryFrame]
  congr 1
  unfold transitionDispatchProgressionDescriptorValues
  rw [List.flatten_eq_flatMap, List.flatMap_assoc]
  conv_rhs => rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro seed hseed
  rw [List.flatMap_map, List.flatMap_assoc]
  simp only [id_eq]
  rfl

/-- The new false descriptor stream is byte-for-byte the established one. -/
theorem verifierTransitionDispatchMuxInvocationLabelMajorFalseFrames_eq_existing
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorFalseFrames W input =
      verifierTransitionDispatchMuxInvocationDescriptorFalseFrames W input := by
  rw [verifierTransitionDispatchMuxInvocationLabelMajorFalseFrames_eq,
    verifierTransitionDispatchMuxInvocationDescriptorFalseFrames_eq,
    verifierTransitionDispatchMuxInvocationLabelMajorFalseProgressions_eq]

noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorFalseMarkedRows_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationLabelMajorFalseMarkedRows W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationLabelMajorFourRowNormalizedFrames_computableInPolyTime
        W)
      (unaryFramePeriodicMarkedRowFilter_computableInPolyTime
        transitionDispatchMuxInvocationLabelMajorFalseSelection
        transitionDispatchMuxInvocationLabelMajorFalseSelection_nonempty)
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteUnaryFramePeriodicMarkedRows
      transitionDispatchMuxInvocationLabelMajorFalseSelection
      transitionDispatchMuxInvocationLabelMajorFalseSelection_nonempty
      (verifierTransitionDispatchMuxInvocationLabelMajorFourRowNormalizedFrames
        W input))
  simpa [Function.comp_def] using Classical.choice composed

noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorFalseFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationLabelMajorFalseFrames W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationLabelMajorFalseMarkedRows_computableInPolyTime
        W)
      unmarkAffineUnaryTripleProgressionRows_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => unmarkAffineUnaryTripleProgressionRows
      (verifierTransitionDispatchMuxInvocationLabelMajorFalseMarkedRows
        W input))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin



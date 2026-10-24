-- Prove2me | Definitions.Def_PricingWithTips3DM_4de718643723c432564de3fd
-- name    : PricingWithTips3DM_4de718643723c432564de3fd
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T01:22:13.29146+00:00
-- url     : https://prove2.me/theorems/4a08eb5f-ed7a-4faa-a0b1-4a9387db86f8
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorSelectorFrames
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_0a2631b4ea0c8335f9d3178e
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Recovering the physical dispatch-mux selector channel

The final four-way descriptor route stores one marked selector row after the
false, true, and coordinate rows of each transition seed.  This module selects
that fourth row and removes its outer marker.  The recovered bytes are proved
equal to the established raw-input selector frame stream.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Keep the selector row and erase the other three routed rows. -/
def transitionDispatchMuxInvocationDescriptorSelectorSelection : List Bool :=
  [false, false, false, true]

theorem transitionDispatchMuxInvocationDescriptorSelectorSelection_nonempty :
    0 < transitionDispatchMuxInvocationDescriptorSelectorSelection.length := by
  simp [transitionDispatchMuxInvocationDescriptorSelectorSelection]

/-- Physical marked stream containing only the selector row of each
transition seed. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorSelectorMarkedRows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFramePeriodicMarkedRows
    transitionDispatchMuxInvocationDescriptorSelectorSelection
    transitionDispatchMuxInvocationDescriptorSelectorSelection_nonempty
    (verifierTransitionDispatchMuxInvocationDescriptorFourWayRows W input)

/-- Periodic selection retains exactly one marked selector row per seed. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorSelectorMarkedRows_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorSelectorMarkedRows
        W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeUnaryFrame (transitionDispatchSelectors W.machine.tm seed) ++
          [.frameEnd] := by
  unfold verifierTransitionDispatchMuxInvocationDescriptorSelectorMarkedRows
  rw [←
    verifierTransitionDispatchMuxInvocationDescriptorFourWayValueGroups_encoding_eq]
  rw [rewriteUnaryFramePeriodicMarkedRows_encode]
  have hgroups : ∀ group ∈
      verifierTransitionDispatchMuxInvocationDescriptorFourWayValueGroups
        W input,
      group.length =
        transitionDispatchMuxInvocationDescriptorSelectorSelection.length := by
    intro group hgroup
    have hlength :=
      verifierTransitionDispatchMuxInvocationDescriptorFourWayValueGroups_length
        W input group hgroup
    simpa [transitionDispatchMuxInvocationDescriptorFalseSelection,
      transitionDispatchMuxInvocationDescriptorSelectorSelection] using
        hlength
  rw [encodeUnaryFramePeriodicMarkedRowOutput_groups
    transitionDispatchMuxInvocationDescriptorSelectorSelection
    transitionDispatchMuxInvocationDescriptorSelectorSelection_nonempty _
    hgroups]
  unfold
    verifierTransitionDispatchMuxInvocationDescriptorFourWayValueGroups
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  simp [transitionDispatchMuxInvocationDescriptorSelectorSelection,
    encodeUnaryFramePeriodicSelectedMarkedRows]

/-- The unified raw descriptor source followed by selector-row selection is
one concrete polynomial-time TM2. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorSelectorMarkedRows_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorSelectorMarkedRows
        W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationDescriptorFourWayRows_computableInPolyTime
        W)
      (unaryFramePeriodicMarkedRowFilter_computableInPolyTime
        transitionDispatchMuxInvocationDescriptorSelectorSelection
        transitionDispatchMuxInvocationDescriptorSelectorSelection_nonempty)
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteUnaryFramePeriodicMarkedRows
      transitionDispatchMuxInvocationDescriptorSelectorSelection
      transitionDispatchMuxInvocationDescriptorSelectorSelection_nonempty
      (verifierTransitionDispatchMuxInvocationDescriptorFourWayRows W input))
  simpa [Function.comp_def] using Classical.choice composed

/-- Ordinary selector frame stream recovered from the selected marked rows. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorSelectorFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  unmarkAffineUnaryTripleProgressionRows
    (verifierTransitionDispatchMuxInvocationDescriptorSelectorMarkedRows
      W input)

/-- Marker removal recovers exactly the established selector source. -/
theorem verifierTransitionDispatchMuxInvocationDescriptorSelectorFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorSelectorFrames W input =
      verifierTransitionDispatchSelectorFrames W input := by
  unfold verifierTransitionDispatchMuxInvocationDescriptorSelectorFrames
  rw [verifierTransitionDispatchMuxInvocationDescriptorSelectorMarkedRows_eq]
  rw [show
      (verifierTransitionRowSeeds W input).flatMap
          (fun seed =>
            encodeUnaryFrame (transitionDispatchSelectors W.machine.tm seed) ++
              [.frameEnd]) =
        ((verifierTransitionRowSeeds W input).map fun seed =>
          transitionDispatchSelectors W.machine.tm seed).flatMap
            (fun row => encodeUnaryFrame row ++ [.frameEnd]) by
      simp [List.flatMap_map]]
  rw [unmarkAffineUnaryTripleProgressionRows_markedValues]
  rw [verifierTransitionDispatchSelectorFrames_eq]
  congr 1

/-- A concrete polynomial-time TM2 follows the unified route, selects the
fourth physical channel, and emits the canonical selector frames. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorSelectorFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorSelectorFrames W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationDescriptorSelectorMarkedRows_computableInPolyTime
        W)
      unmarkAffineUnaryTripleProgressionRows_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => unmarkAffineUnaryTripleProgressionRows
      (verifierTransitionDispatchMuxInvocationDescriptorSelectorMarkedRows
        W input))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin



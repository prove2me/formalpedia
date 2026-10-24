-- Prove2me | Definitions.Def_PricingWithTips3DM_b7a225dc54c0d9001cbf0224
-- name    : PricingWithTips3DM_b7a225dc54c0d9001cbf0224
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T00:50:33.2618+00:00
-- url     : https://prove2.me/theorems/4c1a8718-8cae-467f-9447-db06ffe0b0c7
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorPacketDuplicate
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_20e3cb79b5fd55d3568073bb
import Definitions.Def_PricingWithTips3DM_645fa74d60687a6229a5303d
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Duplicating unified dispatch-mux descriptor packets

After packet marking, every transition row is one physical `frameEnd`-delimited
payload.  This module feeds those rows to the verified duplicator.  Both copies
therefore arise from the same tape packet; the later descriptor interpreter
may route them through independent fixed stages without assuming a semantic
fan-out operation.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

private theorem transitionDispatchMuxInvocationDescriptorValues_ne_nil
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    transitionDispatchMuxInvocationDescriptorValues tm seed ≠ [] := by
  intro hempty
  have hlength :=
    transitionDispatchMuxInvocationDescriptorValues_length tm seed
  rw [hempty] at hlength
  simp only [List.length_nil] at hlength
  have hpositive :=
    transitionDispatchMuxInvocationDescriptorPacketWidth_pos tm
  omega

/-- Typed packet family accepted by the generic marked-row duplicator. -/
noncomputable def verifierTransitionDispatchMuxInvocationDescriptorPacketFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  { rows := (verifierTransitionRowSeeds W input).map fun seed =>
      encodeUnaryFrameFixedWidthPacketBody
        (transitionDispatchMuxInvocationDescriptorValues W.machine.tm seed)
    frameEnd_free := by
      intro row hrow symbol hsymbol
      rw [List.mem_map] at hrow
      rcases hrow with ⟨seed, hseed, rfl⟩
      exact encodeUnaryFrameFixedWidthPacketBody_frameEnd_free _ symbol
        hsymbol }

/-- The typed duplicator input is byte-for-byte the packet stream already
compiled from the original verifier word. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorPacketFamily_encoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeUnaryFrameMarkedRowFamily
        (verifierTransitionDispatchMuxInvocationDescriptorPacketFamily
          W input) =
      verifierTransitionDispatchMuxInvocationDescriptorPacketFrames
        W input := by
  rw [verifierTransitionDispatchMuxInvocationDescriptorPacketFrames_eq]
  unfold encodeUnaryFrameMarkedRowFamily
    verifierTransitionDispatchMuxInvocationDescriptorPacketFamily
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  have hne := transitionDispatchMuxInvocationDescriptorValues_ne_nil
    W.machine.tm seed
  cases hvalues :
      transitionDispatchMuxInvocationDescriptorValues W.machine.tm seed with
  | nil => exact False.elim (hne hvalues)
  | cons value values =>
      simpa only [Function.comp_apply, hvalues] using
        (encodeUnaryFrameFixedWidthPacket_eq_body value values).symm

/-- Concrete stream containing two consecutive physical copies of every
complete transition-row descriptor packet. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorDuplicatedPacketFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  encodeUnaryFrameDuplicatedMarkedRowFamily
    (verifierTransitionDispatchMuxInvocationDescriptorPacketFamily W input)

/-- Exact seed-major semantics of the duplicated packet source. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorDuplicatedPacketFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorDuplicatedPacketFrames
        W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        let packet := encodeUnaryFrameFixedWidthPacket
          (transitionDispatchMuxInvocationDescriptorValues W.machine.tm seed)
        packet ++ packet := by
  unfold
    verifierTransitionDispatchMuxInvocationDescriptorDuplicatedPacketFrames
    encodeUnaryFrameDuplicatedMarkedRowFamily
    verifierTransitionDispatchMuxInvocationDescriptorPacketFamily
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  have hne := transitionDispatchMuxInvocationDescriptorValues_ne_nil
    W.machine.tm seed
  cases hvalues :
      transitionDispatchMuxInvocationDescriptorValues W.machine.tm seed with
  | nil => exact False.elim (hne hvalues)
  | cons value values =>
      rw [show encodeUnaryFrameFixedWidthPacket (value :: values) =
          encodeUnaryFrameFixedWidthPacketBody (value :: values) ++
            [.frameEnd] by
        exact encodeUnaryFrameFixedWidthPacket_eq_body value values]
      simp [List.append_assoc]

/-- One continuous polynomial-time pipeline now packetizes and duplicates the
unified mux descriptors from the original verifier word. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorDuplicatedPacketFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorDuplicatedPacketFrames
        W) := by
  let packetSource :=
    verifierTransitionDispatchMuxInvocationDescriptorPacketFrames_computableInPolyTime
      W
  let typedPacketSource :
      _root_.Turing.TM2ComputableInPolyTime id
        encodeUnaryFrameMarkedRowFamily
        (verifierTransitionDispatchMuxInvocationDescriptorPacketFamily W) :=
    { tm := packetSource.tm
      inputAlphabet := packetSource.inputAlphabet
      outputAlphabet := packetSource.outputAlphabet
      time := packetSource.time
      outputsFun := fun input => by
        have run := packetSource.outputsFun input
        simpa only [id_eq,
          verifierTransitionDispatchMuxInvocationDescriptorPacketFamily_encoding_eq
            W input] using run }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      typedPacketSource unaryFrameMarkedRowDuplicate_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List Γ =>
      encodeUnaryFrameDuplicatedMarkedRowFamily
        (verifierTransitionDispatchMuxInvocationDescriptorPacketFamily
          W input))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin



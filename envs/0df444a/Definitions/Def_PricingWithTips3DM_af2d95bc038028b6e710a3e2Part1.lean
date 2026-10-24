-- Prove2me | Definitions.Def_PricingWithTips3DM_af2d95bc038028b6e710a3e2Part1
-- name    : PricingWithTips3DM_af2d95bc038028b6e710a3e2Part1
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T23:23:57.198353+00:00
-- url     : https://prove2.me/theorems/e4fcb0a9-2089-4f60-addc-b84292f3dece
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowInputCompiler.Part1
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_91f6924c35f8535a07903e7f
import Definitions.Def_PricingWithTips3DM_bbaac3743d036b03526ad1a7
import Definitions.Def_PricingWithTips3DM_45e9f4d986c09a37e9b0433c
import Definitions.Def_PricingWithTips3DM_e739c94105fd2664218f136d
import Definitions.Def_PricingWithTips3DM_e6d41fe360e05df340f3315b
import Definitions.Def_PricingWithTips3DM_9799dcd413bccd73aac537c1
import Definitions.Def_PricingWithTips3DM_9e285c891e428168c2c63a3c
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Three delimiter-bearing fragments owned by one validity-row invocation. -/
structure ValidityRowOperandPacket where
  oneHotPrefix : List UnaryFrameSym
  halted : List UnaryFrameSym
  tail : List UnaryFrameSym
deriving DecidableEq, Repr

/-- Concatenate one row's fragments in complete-controller consumption order. -/
def encodeValidityRowOperandPacket
    (packet : ValidityRowOperandPacket) : List UnaryFrameSym :=
  packet.oneHotPrefix ++ packet.halted ++ packet.tail

/-- Canonical fragment packet of one already expanded validity row. -/
def validityRowOperandPacket
    (frame : AffineValidityRowFrame) : ValidityRowOperandPacket :=
  { oneHotPrefix :=
      .tick :: (encodeAffineExactlyOneFamily frame.oneHotFrames ++
        [.frameEnd])
    halted :=
      encodeUnaryFrame
        [frame.haltedStart, frame.haltedLeft, frame.haltedRight] ++
          [.frameEnd]
    tail := encodeAffineValidityTailFrame frame.tailFrame }

/-- Row packets for the canonical verifier validity-frame family. -/
def verifierValidityRowOperandPackets
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List ValidityRowOperandPacket :=
  (verifierValidityRowFramesByLength W input.length).map
    validityRowOperandPacket

/-- Packet-family encoding, including the outer family terminator. -/
def encodeValidityRowOperandPacketFamily
    (packets : List ValidityRowOperandPacket) : List UnaryFrameSym :=
  packets.flatMap encodeValidityRowOperandPacket ++ [.frameEnd]

/-- Direct row-seed specification of the complete family input.  This is the
semantic output target for the remaining fixed source controller. -/
def validityRowSeedFamilyInput (tm : _root_.Turing.FinTM2) :
    List ValidityRowSeed → List UnaryFrameSym
  | [] => [.frameEnd]
  | seed :: rest =>
      .tick ::
        (encodeAffineValidityRowFrame (expandValidityRowSeed tm seed) ++
          validityRowSeedFamilyInput tm rest)

/-- The recursive seed target is exactly the established family encoding. -/
theorem validityRowSeedFamilyInput_eq
    (tm : _root_.Turing.FinTM2) (seeds : List ValidityRowSeed) :
    validityRowSeedFamilyInput tm seeds =
      encodeAffineValidityRowFamilyInput
        (seeds.map (expandValidityRowSeed tm)) := by
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp [validityRowSeedFamilyInput,
        encodeAffineValidityRowFamilyInput,
        encodeAffineValidityRowFamily, ih, List.append_assoc]

/-- Raw-verifier specialization of the complete row-family target. -/
def verifierValidityRowFamilyInputTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  validityRowSeedFamilyInput W.machine.tm
    (verifierValidityRowSeeds W input)

/-- The seed target is byte-for-byte the canonical complete family input. -/
theorem verifierValidityRowFamilyInputTarget_eq_canonical
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowFamilyInputTarget W input =
      encodeAffineValidityRowFamilyInput
        (verifierValidityRowFramesByLength W input.length) := by
  unfold verifierValidityRowFamilyInputTarget
  rw [validityRowSeedFamilyInput_eq,
    verifierValidityRowSeeds_expand_eq_frames]

/-- The complete family encoding is literally the row-packet encoding. -/
theorem verifierValidityRowFamilyInputTarget_eq_packets
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowFamilyInputTarget W input =
      encodeValidityRowOperandPacketFamily
        (verifierValidityRowOperandPackets W input) := by
  rw [verifierValidityRowFamilyInputTarget_eq_canonical]
  unfold verifierValidityRowOperandPackets
  generalize verifierValidityRowFramesByLength W input.length = frames
  induction frames with
  | nil => rfl
  | cons frame rest ih =>
      simp [encodeAffineValidityRowFamilyInput,
        encodeAffineValidityRowFamily,
        encodeValidityRowOperandPacketFamily,
        encodeValidityRowOperandPacket, validityRowOperandPacket,
        encodeAffineValidityRowFrame, List.append_assoc]
      exact List.append_cancel_right ih

/-- The concrete one-hot source is the first projection of the synchronized
canonical packet list. -/
theorem verifierValidityRowOperandPackets_oneHot
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierValidityRowOperandPackets W input).flatMap
        (fun packet => packet.oneHotPrefix) =
      verifierValidityRowOneHotMarkedOperandFrames W input := by
  rw [verifierValidityRowOneHotMarkedOperandFrames_eq_canonical]
  simp [verifierValidityRowOperandPackets, validityRowOperandPacket,
    List.flatMap_map]

/-- The concrete halted source is the second projection of the synchronized
canonical packet list. -/
theorem verifierValidityRowOperandPackets_halted
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierValidityRowOperandPackets W input).flatMap
        (fun packet => packet.halted) =
      verifierValidityRowHaltedMarkedOperandFrames W input := by
  rw [verifierValidityRowHaltedMarkedOperandFrames_eq_frames]
  simp [verifierValidityRowOperandPackets, validityRowOperandPacket,
    List.flatMap_map]

/-- The concrete tail source is the third projection of the synchronized
canonical packet list. -/
theorem verifierValidityRowOperandPackets_tail
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierValidityRowOperandPackets W input).flatMap
        (fun packet => packet.tail) =
      verifierValidityRowTailOperandFrames W input := by
  rw [verifierValidityRowTailOperandFrames_eq_canonical]
  simp [verifierValidityRowOperandPackets, validityRowOperandPacket,
    List.flatMap_map]
end CLRS.Chapter34.Turing.CookLevin



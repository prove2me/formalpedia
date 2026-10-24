-- Prove2me | Definitions.Def_PricingWithTips3DM_8f19129848b25a45a212d372
-- name    : PricingWithTips3DM_8f19129848b25a45a212d372
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:30:49.606885+00:00
-- url     : https://prove2.me/theorems/083a92d0-29e7-4ef1-a235-cdeaaa385a83
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameLengthPrefixedFourWaySplitBounds
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_cfe2ea8dd1a1f99140637e4f
import Mathlib.Tactic
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Linear bounds for the dynamic four-way splitter

The input itself contains every unary payload symbol and enough separators to
pay for the counter operations.  Consequently the complete fixed controller
has a uniform linear bound in the concrete source-stream length.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Every unary field contributes at least its terminating separator. -/
theorem length_le_encodeUnaryFrame_length (values : List Nat) :
    values.length ≤ (encodeUnaryFrame values).length := by
  rw [encodeUnaryFrame_length]
  induction values with
  | nil => simp
  | cons value values ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega

/-- Exact concrete source length of one self-described packet. -/
theorem UnaryFrameLengthPrefixedFourWayPacket.sourceFrames_length
    (packet : UnaryFrameLengthPrefixedFourWayPacket) :
    packet.sourceFrames.length =
      packet.width + 1 + (packet.selector + 1) +
        (encodeUnaryFrame packet.coordinates).length +
        (encodeUnaryFrame packet.whenTrue).length +
        (encodeUnaryFrame packet.whenFalse).length + 1 := by
  simp [UnaryFrameLengthPrefixedFourWayPacket.sourceFrames,
    encodeUnaryFrameLengthPrefixedFourWaySplitInput,
    encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc]
  omega

/-- One packet costs at most six builder steps per concrete input symbol. -/
theorem UnaryFrameLengthPrefixedFourWayPacket.steps_le_sourceFrames
    (packet : UnaryFrameLengthPrefixedFourWayPacket) :
    packet.steps ≤ 6 * packet.sourceFrames.length := by
  have hcoordinates := length_le_encodeUnaryFrame_length packet.coordinates
  have htrue := length_le_encodeUnaryFrame_length packet.whenTrue
  have hfalse := length_le_encodeUnaryFrame_length packet.whenFalse
  rw [packet.coordinates_length] at hcoordinates
  rw [packet.whenTrue_length] at htrue
  rw [packet.whenFalse_length] at hfalse
  rw [packet.sourceFrames_length]
  simp only [UnaryFrameLengthPrefixedFourWayPacket.steps,
    unaryFrameLengthPrefixedFourWaySplitPacketSteps,
    unaryFrameLengthPrefixedFourWaySplitSectionSteps]
  rw [packet.coordinates_length, packet.whenTrue_length,
    packet.whenFalse_length]
  omega

/-- Family body steps are linear in the actual concatenated source. -/
theorem unaryFrameLengthPrefixedFourWayPacketFamilySteps_le
    (packets : List UnaryFrameLengthPrefixedFourWayPacket) :
    unaryFrameLengthPrefixedFourWayPacketFamilySteps packets ≤
      6 * (encodeUnaryFrameLengthPrefixedFourWayPacketFamily packets).length := by
  induction packets with
  | nil => simp [unaryFrameLengthPrefixedFourWayPacketFamilySteps,
      encodeUnaryFrameLengthPrefixedFourWayPacketFamily]
  | cons packet rest ih =>
      have hpacket := packet.steps_le_sourceFrames
      rw [unaryFrameLengthPrefixedFourWayPacketFamilySteps]
      have hsource :
          encodeUnaryFrameLengthPrefixedFourWayPacketFamily (packet :: rest) =
            packet.sourceFrames ++
              encodeUnaryFrameLengthPrefixedFourWayPacketFamily rest := rfl
      rw [hsource, List.length_append]
      omega

end CLRS.Chapter34.Turing.PolyBuilder



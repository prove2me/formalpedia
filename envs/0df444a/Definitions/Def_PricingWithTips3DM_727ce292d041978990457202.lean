-- Prove2me | Definitions.Def_PricingWithTips3DM_727ce292d041978990457202
-- name    : PricingWithTips3DM_727ce292d041978990457202
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:24:59.801344+00:00
-- url     : https://prove2.me/theorems/183996ed-4c43-42e2-b25e-753eb4696ce3
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameFixedWidthPacketNormalize
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_514831e2fc5be01dfafd65e4
import Definitions.Def_PricingWithTips3DM_3799fd79c9b0b4d68c438353
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Normalizing marked fixed-width packets

The one-symbol packet marker replaces a packet's last ordinary separator by
`frameEnd`.  Row-oriented consumers use the standard representation in which
that separator is retained and the outer marker follows it.  This module
supplies the fixed symbol-local expansion between the two formats.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Restore an ordinary final field delimiter before every physical packet
marker. -/
def unaryFrameFixedWidthPacketNormalizeBody :
    LoopBody UnaryFrameSym UnaryFrameSym where
  emit
    | .tick => [.tick]
    | .separator => [.separator]
    | .frameEnd => [.separator, .frameEnd]
  cost
    | .tick => 1
    | .separator => 1
    | .frameEnd => 2
  emit_length_le_cost := by
    intro symbol
    cases symbol <;> simp

/-- Forward standardization of all packet boundaries. -/
def restoreUnaryFrameFixedWidthPacketSeparators
    (input : List UnaryFrameSym) : List UnaryFrameSym :=
  input.flatMap unaryFrameFixedWidthPacketNormalizeBody.emit

private theorem packetNormalize_ticks (count : Nat) :
    (List.replicate count UnaryFrameSym.tick).flatMap
        unaryFrameFixedWidthPacketNormalizeBody.emit =
      List.replicate count UnaryFrameSym.tick := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, List.flatMap_cons, ih]
      rfl

/-- One nonempty compact packet becomes the canonical ordinary unary row
followed by its outer marker. -/
theorem restoreUnaryFrameFixedWidthPacketSeparators_encode
    (value : Nat) (values : List Nat) :
    restoreUnaryFrameFixedWidthPacketSeparators
        (encodeUnaryFrameFixedWidthPacket (value :: values)) =
      encodeUnaryFrame (value :: values) ++ [.frameEnd] := by
  induction values generalizing value with
  | nil =>
      simp only [restoreUnaryFrameFixedWidthPacketSeparators,
        encodeUnaryFrameFixedWidthPacket, List.flatMap_append,
        List.flatMap_cons, List.flatMap_nil]
      rw [packetNormalize_ticks]
      simp [unaryFrameFixedWidthPacketNormalizeBody, encodeUnaryFrame,
        encodeUnaryFrameBlock, List.append_assoc]
  | cons next rest ih =>
      simp only [restoreUnaryFrameFixedWidthPacketSeparators,
        encodeUnaryFrameFixedWidthPacket, List.flatMap_append,
        List.flatMap_cons]
      rw [packetNormalize_ticks]
      change List.replicate value .tick ++
          .separator ::
            restoreUnaryFrameFixedWidthPacketSeparators
              (encodeUnaryFrameFixedWidthPacket (next :: rest)) = _
      rw [ih]
      simp [encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc]

/-- Exact normalization of any nonempty packet family. -/
theorem restoreUnaryFrameFixedWidthPacketSeparators_family
    (packets : List (List Nat))
    (hnonempty : ∀ packet ∈ packets, packet ≠ []) :
    restoreUnaryFrameFixedWidthPacketSeparators
        (packets.flatMap encodeUnaryFrameFixedWidthPacket) =
      packets.flatMap fun packet =>
        encodeUnaryFrame packet ++ [.frameEnd] := by
  unfold restoreUnaryFrameFixedWidthPacketSeparators
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro packet hpacket
  have hne := hnonempty packet hpacket
  cases packet with
  | nil => exact False.elim (hne rfl)
  | cons value values =>
      exact restoreUnaryFrameFixedWidthPacketSeparators_encode value values

/-- The packet normalizer is one concrete linear-time TM2. -/
noncomputable def
    restoreUnaryFrameFixedWidthPacketSeparators_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      restoreUnaryFrameFixedWidthPacketSeparators := by
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List UnaryFrameSym =>
      input.flatMap unaryFrameFixedWidthPacketNormalizeBody.emit)
  exact boundedLoop_computableInPolyTime
    unaryFrameFixedWidthPacketNormalizeBody

end CLRS.Chapter34.Turing.PolyBuilder



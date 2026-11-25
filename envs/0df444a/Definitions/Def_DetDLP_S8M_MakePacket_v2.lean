-- Prove2me | Definitions.Def_DetDLP_S8M_MakePacket_v2
-- name    : DetDLP_S8M_MakePacket_v2
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T03:30:08.66599+00:00
-- url     : https://prove2.me/theorems/0fef0fe6-c35c-49bb-b808-511af626234c
-- title:
--   Polynomial EC pair packet builder and size realization
-- statement:
--   Polynomial packet constructor and exact encoded subdivision-instance identity with the Bounds scale for EC pair queries.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8M_BaseFits
import Definitions.Def_DetDLP_S8M_SubPoly
import Definitions.Def_DetDLP_S8M_Bounds
import Definitions.Def_DetDLP_S8M_ECPairPacket

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 1200000

namespace DetDLP.S8M.MakePacketV2

open Groundwork S8C S8H w4_M5Network
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

abbrev W := List Bool
abbrev Addresses := S8G.FpMoment.Code.Addresses

/-- The packet scale used by the deterministic EC-pair realization theorem. -/
def sizeField (w : W) := DetDLP.S8M.Bounds.scale
  (S8G.FpMoment.Code.slots (S8G.FpMoment.Code.width (DetDLP.S8M.ECPair.Packet.prime w)))
  (S8G.FpMoment.Code.width (DetDLP.S8M.ECPair.Packet.prime w))

/-- Build the encoded subdivision instance using the supplied numeric address
model. -/
def make (a : Addresses) (w : W) := outerPacket w
  (WirePacket.packet (a.nv w) (a.ne w) (a.src w) (a.dst w)) (sizeField w)

attribute [local fun_prop] PolyT.fst PolyT.snd PolyT.comp PolyT.prodMk PolyT.id' PolyT.const
  PolyT.mul S8G.FpMoment.Code.width_poly S8G.FpMoment.Code.slots_poly
  DetDLP.S8M.ECPair.Packet.prime_poly
  P2M_Groundwork_PolyT_id__1c5d0f44cc8f

theorem sizeField_poly : PolyT sizeField := by
  unfold sizeField DetDLP.S8M.Bounds.scale
  fun_prop

theorem make_poly (a : Addresses) (h : a.Uniform) : PolyT (make a) :=
  outerPacket_poly PolyT.id'
    (WirePacket.packet_poly h.nv h.ne h.vert h.edge h.src h.dst) sizeField_poly

variable {p m : ℕ} [Fact p.Prime]
variable (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
variable (T : ℕ) (S : ECSeed p m) (X : E.toAffine.Point) (η : W)

theorem sizeField_word :
    sizeField (DetDLP.S8M.ECPair.word E T S X η) =
      DetDLP.S8M.Bounds.scale (blockCount (bitLen p)) (bitLen p) := by
  simp [sizeField, DetDLP.S8M.ECPair.Packet.fields, S8G.FpMoment.Code.width_eq,
    S8G.FpMoment.Code.slots_eq]

theorem make_word (a : Addresses) (G : WireGraph)
    (hv : a.nv (DetDLP.S8M.ECPair.word E T S X η) = G.nV)
    (he : a.ne (DetDLP.S8M.ECPair.word E T S X η) = G.nE)
    (hs : ∀ i : Fin G.nE, a.src (DetDLP.S8M.ECPair.word E T S X η) i.val = (G.endpoints i).1.val)
    (hd : ∀ i : Fin G.nE, a.dst (DetDLP.S8M.ECPair.word E T S X η) i.val = (G.endpoints i).2.val) :
    let w := DetDLP.S8M.ECPair.word E T S X η
    let s := DetDLP.S8M.Bounds.scale (blockCount (bitLen p)) (bitLen p)
    make a w = encodeBTNInstance w G.subdivision s s 1 := by
  dsimp only [make]
  rw [hv, he, WirePacket.packet_eq G _ _ hs hd, sizeField_word, outerPacket_eq]

end DetDLP.S8M.MakePacketV2



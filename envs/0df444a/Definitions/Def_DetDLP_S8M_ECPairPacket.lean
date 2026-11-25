-- Prove2me | Definitions.Def_DetDLP_S8M_ECPairPacket
-- name    : DetDLP_S8M_ECPairPacket
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T05:49:36.321222+00:00
-- url     : https://prove2.me/theorems/b358299b-5577-4415-993d-07b07b7704ed
-- title:
--   Uniform Tag 6 graph and local port encoders
-- statement:
--   The EC pair query fields decode exactly on Tag 6 inputs. Given uniform graph addresses, the packet functions are polynomial time and encode the correct subdivision, size and local response.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_S8M_ECPairGraph
import Definitions.Def_DetDLP_S8G_FpMomentPoly

set_option autoImplicit false
namespace DetDLP.S8M.ECPair.Packet
open M89S1 Groundwork DetDLP_W1_Queries S8C S8H w4_M5Network
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
abbrev W := List Bool
abbrev Addresses := S8G.FpMoment.Code.Addresses

def prime (w : W) := PolyT.bval (first (second w))
def threshold (w : W) := PolyT.bval (third w)
def seed (w : W) := third (more w)
def target (w : W) := third (more (more w))
def prefixBits (w : W) := third (more (more (more w)))

attribute [local fun_prop] PolyT.fst PolyT.snd PolyT.comp PolyT.prodMk PolyT.id' PolyT.const
  first_poly more_poly PolyT.length PolyT.mul S8G.FpMoment.Code.width_poly S8G.FpMoment.Code.slots_poly
  P2M_Groundwork_PolyT_id__1c5d0f44cc8f

@[local fun_prop] theorem prime_poly : PolyT prime := by unfold prime second; fun_prop
@[local fun_prop] theorem threshold_poly : PolyT threshold := by unfold threshold third second; fun_prop
@[local fun_prop] theorem seed_poly : PolyT seed := by unfold seed third second; fun_prop
@[local fun_prop] theorem target_poly : PolyT target := by unfold target third second; fun_prop
@[local fun_prop] theorem prefix_poly : PolyT prefixBits := by unfold prefixBits third second; fun_prop

def sizeField (w : W) := scale (S8G.FpMoment.Code.slots (S8G.FpMoment.Code.width (prime w))) (S8G.FpMoment.Code.width (prime w))
@[local fun_prop] theorem sizeField_poly : PolyT sizeField := by unfold sizeField scale; fun_prop

def make (a : Addresses) (w : W) := outerPacket w
  (WirePacket.packet (a.nv w) (a.ne w) (a.src w) (a.dst w)) (sizeField w)
abbrev port := S8G.FpMoment.Code.port

theorem make_poly (a : Addresses) (h : a.Uniform) : PolyT (make a) :=
  outerPacket_poly PolyT.id' (WirePacket.packet_poly h.nv h.ne h.vert h.edge h.src h.dst) sizeField_poly

theorem port_poly (a : Addresses) (h : a.Uniform) : PolyT (port a) := S8G.FpMoment.Code.port_poly a h

variable {p m : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (T : ℕ) (S : ECSeed p m)
  (X : E.toAffine.Point) (η : W)

@[simp] theorem fields : let w := word E T S X η
    prime w = p ∧ threshold w = T ∧ seed w = List.ofFn (ecBits S) ∧
    target w = encodeNatListBin (pointCoords X) ∧ prefixBits w = η := by
  simp [prime,threshold,seed,target,prefixBits,second,third,word,queryWord,encodeCurveInput,encodeNatListBin]

theorem sizeField_word : sizeField (word E T S X η) = scale (blockCount (bitLen p)) (bitLen p) := by
  simp only [sizeField,(fields E T S X η).1,S8G.FpMoment.Code.width_eq,S8G.FpMoment.Code.slots_eq]

theorem make_word (a : Addresses) (G : WireGraph)
    (hv : a.nv (word E T S X η) = G.nV) (he : a.ne (word E T S X η) = G.nE)
    (hs : ∀ i : Fin G.nE, a.src (word E T S X η) i.val = (G.endpoints i).1.val)
    (hd : ∀ i : Fin G.nE, a.dst (word E T S X η) i.val = (G.endpoints i).2.val) :
    let w := word E T S X η; let s := scale (blockCount (bitLen p)) (bitLen p)
    make a w = encodeBTNInstance w G.subdivision s s 1 := by
  dsimp only
  rw [make,hv,he,WirePacket.packet_eq G _ _ hs hd,sizeField_word,outerPacket_eq]

theorem port_word (a : Addresses) (w : W) (v : ℕ) (xs : W) :
    port a (encodePortQuery w v xs) = encodeNatListBin [if a.check (w,v,xs) then 1 else 0] :=
  S8G.FpMoment.Code.port_word a w v xs

end DetDLP.S8M.ECPair.Packet



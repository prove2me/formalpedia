-- Prove2me | Definitions.Def_DetDLP_S8C_Packet
-- name    : DetDLP_S8C_Packet
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T04:25:31.333749+00:00
-- url     : https://prove2.me/theorems/b43ede79-f943-4727-ac0f-e676f1c1831c
-- title:
--   Polynomial-time Boolean graph and port packets
-- statement:
--   Canonical graph encoding is polynomial time from unary dimension bounds and polynomial-time indexed side and endpoint functions. The outer builder and the port response wrap this graph and local test in the exact problem encoding.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_BTN
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_DetDLP_W1_Queries
import Definitions.Def_DetDLP_W5_M6Sort

set_option autoImplicit false
namespace DetDLP.S8C
open Groundwork
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
abbrev PacketWord := List Bool
attribute [local fun_prop] PolyT.comp PolyT.const PolyT.fst PolyT.snd PolyT.prodMk PolyT.flatMap PolyT.map PolyT.id'
  P2M_Groundwork_PolyT_cons__3a60f43a3b86 P2M_Groundwork_PolyT_id__1c5d0f44cc8f
  DetDLP_W1_Queries.frame_poly DetDLP_W1_Queries.first_poly DetDLP_W1_Queries.more_poly
  w5_M6Sort.cw_poly w5_M6Sort.encode_poly

/-- Enumerate the actual side bits and flattened endpoint pairs in canonical order. -/
def graphPacket (nv ne : ℕ) (side : ℕ → Bool) (src dst : ℕ → ℕ) : PacketWord :=
  Encoding.encodeList id [countWord nv,countWord ne,(List.range nv).map side,
    encodeNatListBin ((List.range ne).flatMap fun i => [src i,dst i])]

theorem graphPacket_eq (G : BipartiteMultigraph) (side : ℕ → Bool) (src dst : ℕ → ℕ)
    (hv : ∀ i : Fin G.nV, side i.val = G.side i)
    (hs : ∀ i : Fin G.nE, src i.val = (G.endpoints i).1.val)
    (hd : ∀ i : Fin G.nE, dst i.val = (G.endpoints i).2.val) :
    graphPacket G.nV G.nE side src dst = G.encode := by
  unfold graphPacket BipartiteMultigraph.encode
  have r (n : ℕ) : List.range n = (List.finRange n).map Fin.val := by simp
  simp only [r,List.map_map,List.flatMap_map,Function.comp_def,hv,hs,hd,List.ofFn_eq_map]

section Poly
variable {α : Type} [Enc α]

theorem graphPacket_poly {nv ne : α → ℕ} {side : α → ℕ → Bool} {src dst : α → ℕ → ℕ}
    (hnv : PolyT nv) (hne : PolyT ne) (unv : Unary nv) (une : Unary ne)
    (hside : PolyT fun z : α × ℕ => side z.1 z.2) (hsrc : PolyT fun z : α × ℕ => src z.1 z.2)
    (hdst : PolyT fun z : α × ℕ => dst z.1 z.2) :
    PolyT (fun x => graphPacket (nv x) (ne x) (side x) (src x) (dst x)) := by
  have hsi := PolyT.map hside (PolyT.range unv)
  have hep := PolyT.flatMap (f := fun x i => [src x i,dst x i]) (by fun_prop) (PolyT.range une)
  simp only [graphPacket,Encoding.encodeList,id_eq,← DetDLP_W1_Queries.frame_correct]
  fun_prop (disch := assumption)

/-- Outer query packet. Size and coefficient precision share the same scale. -/
def outerPacket (desc graph : PacketWord) (s : ℕ) :=
  Encoding.encodeList id [desc,graph,countWord s,countWord s,countWord 1]

@[local fun_prop] theorem outerPacket_poly {d g : α → PacketWord} {s : α → ℕ}
    (hd : PolyT d) (hg : PolyT g) (hs : PolyT s) : PolyT (fun x => outerPacket (d x) (g x) (s x)) := by
  simp only [outerPacket,Encoding.encodeList,id_eq,← DetDLP_W1_Queries.frame_correct]; fun_prop

theorem outerPacket_eq (w : PacketWord) (G : BipartiteMultigraph) (s : ℕ) :
    outerPacket w G.encode s = encodeBTNInstance w G s s 1 := rfl

end Poly

/-- Invoke a numeric local checker on the three framed port arguments. -/
def portPacket (check : PacketWord × ℕ × PacketWord → Bool) (z : PacketWord) :=
  encodeNatListBin [if check (DetDLP_W1_Queries.first z,PolyT.bval (DetDLP_W1_Queries.second z),DetDLP_W1_Queries.third z) then 1 else 0]

theorem portPacket_eq (check : PacketWord × ℕ × PacketWord → Bool) (w : PacketWord) (v : ℕ) (a : PacketWord) :
    portPacket check (encodePortQuery w v a) = encodeNatListBin [if check (w,v,a) then 1 else 0] := by
  simp [portPacket,encodePortQuery,DetDLP_W1_Queries.second,DetDLP_W1_Queries.third]

theorem portPacket_poly {check : PacketWord × ℕ × PacketWord → Bool} (h : PolyT check) : PolyT (portPacket check) := by
  have hc : PolyT fun z : PacketWord => check (DetDLP_W1_Queries.first z,PolyT.bval (DetDLP_W1_Queries.second z),DetDLP_W1_Queries.third z) := by
    apply PolyT.comp h; unfold DetDLP_W1_Queries.third DetDLP_W1_Queries.second; fun_prop
  unfold portPacket
  apply w5_M6Sort.encode_poly
  apply P2M_Groundwork_PolyT_cons__3a60f43a3b86 _ (PolyT.const _)
  exact PolyT.ite' (by simpa using hc) (PolyT.const _) (PolyT.const _)

end DetDLP.S8C



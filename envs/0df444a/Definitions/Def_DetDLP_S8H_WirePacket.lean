-- Prove2me | Definitions.Def_DetDLP_S8H_WirePacket
-- name    : DetDLP_S8H_WirePacket
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T05:19:05.394704+00:00
-- url     : https://prove2.me/theorems/59eb6e80-32f8-4db6-9bfe-fb6a16ce2ad9
-- title:
--   Polynomial-time subdivision packets for wire networks
-- statement:
--   The packet enumerates the two half-edge blocks of the subdivision of a loopless wire graph. It agrees with the canonical graph word and is polynomial-time when its vertex and edge ranges are unary-bounded and its endpoint functions are polynomial-time. The realization lemma combines that packet and a local checker with a parsimonious assignment equivalence and the required size bounds.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_S8C_Packet
import Definitions.Def_DetDLP_S8C_WireBTN

set_option autoImplicit false
namespace DetDLP.S8H.WirePacket
attribute [-simp] Fin.natAdd_eq_addNat
open S8C w4_M5Network Groundwork
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

def packet (nv ne : ℕ) (src dst : ℕ → ℕ) :=
  graphPacket (nv+ne) (ne+ne) (fun v => decide (nv ≤ v))
    (fun e => if e < ne then src e else dst (e-ne))
    (fun e => nv + (if e < ne then e else e-ne))

theorem packet_eq (G : WireGraph) (src dst : ℕ → ℕ)
    (hs : ∀ i : Fin G.nE, src i.val = (G.endpoints i).1.val)
    (hd : ∀ i : Fin G.nE, dst i.val = (G.endpoints i).2.val) :
    packet G.nV G.nE src dst = G.subdivision.encode := by
  apply graphPacket_eq G.subdivision
  · intro i; induction i using Fin.addCases with
    | left v => simp [WireGraph.subdivision,v.isLt]
    | right e => simp [WireGraph.subdivision]
  · intro i; induction i using Fin.addCases with
    | left e => simp [WireGraph.subdivision,e.isLt,hs]
    | right e => simp [WireGraph.subdivision,hd]
  · intro i; induction i using Fin.addCases with
    | left e => simp [WireGraph.subdivision,e.isLt]
    | right e => simp [WireGraph.subdivision]

attribute [local fun_prop] PolyT.comp PolyT.const PolyT.prodMk PolyT.fst PolyT.snd PolyT.id'
  P2M_Groundwork_PolyT_id__1c5d0f44cc8f

theorem packet_poly {α : Type} [Enc α] {nv ne : α → ℕ} {src dst : α → ℕ → ℕ}
    (hv : PolyT nv) (he : PolyT ne) (u : Unary fun x => nv x+ne x)
    (u' : Unary fun x => ne x+ne x) (hs : PolyT fun x : α × ℕ => src x.1 x.2)
    (hd : PolyT fun x : α × ℕ => dst x.1 x.2) :
    PolyT fun x => packet (nv x) (ne x) (src x) (dst x) := by
  have hne : PolyT fun x : α × ℕ => ne x.1 := PolyT.comp he (by fun_prop)
  have hnv : PolyT fun x : α × ℕ => nv x.1 := PolyT.comp hv (by fun_prop)
  apply graphPacket_poly (by fun_prop) (by fun_prop) u u'
  · fun_prop
  · apply PolyT.ite' (c := fun x : α × ℕ => x.2 < ne x.1) (by fun_prop) hs
    exact PolyT.comp hd (g := fun x : α × ℕ => (x.1,x.2-ne x.1)) (by fun_prop)
  · apply PolyT.add hnv
    apply PolyT.ite' (c := fun x : α × ℕ => x.2 < ne x.1) <;> fun_prop

theorem realizes (nv ne scale : PacketWord → ℕ) (src dst : PacketWord → ℕ → ℕ)
    (check : PacketWord × ℕ × PacketWord → Bool) (L b : ℕ) (w : PacketWord)
    (G : WireGraph) (T : WireTest G) {A : Type} [Fintype A]
    (e : {x // G.Satisfies T x} ≃ A) (hnv : nv w = G.nV) (hne : ne w = G.nE)
    (hsr : ∀ i : Fin G.nE, src w i.val = (G.endpoints i).1.val)
    (hds : ∀ i : Fin G.nE, dst w i.val = (G.endpoints i).2.val)
    (hs : 2 ≤ scale w) (hb : b ≤ scale w) (he : 2*G.nE < scale w)
    (hv : G.nV+G.nE ≤ (scale w)^L)
    (hd : max (Finset.univ.sup G.deg) 2 ≤ Nat.ceil ((scale w : ℝ)^((9 : ℝ)/10)))
    (h1 : scale w + w.length ≤ L * blockCount b * b) (h2 : scale w + w.length ≤ L*(b+1)^L)
    (hl : ∀ (v : Fin G.subdivision.nV) (a : Fin (G.subdivision.deg v) → Bool),
      (encodePortQuery w v.val (List.ofFn a)).length ≤ L*(scale w+w.length+1)^L)
    (hc : ∀ (v : Fin G.subdivision.nV) (a : Fin (G.subdivision.deg v) → Bool),
      check (w,v.val,List.ofFn a) = G.subdivisionTensor T v a) :
    Realizes (fun z => outerPacket z (packet (nv z) (ne z) (src z) (dst z)) (scale z))
      (portPacket check) L w b (Fintype.card A) := by
  apply wireRealizes _ _ _ (scale w) _ _ G T e hs hb he hv hd h1 h2
  · simp only [hnv,hne,packet_eq G _ _ hsr hds]; rfl
  · intro v a; exact ⟨hl v a,by rw [portPacket_eq,hc]⟩

end DetDLP.S8H.WirePacket



-- Prove2me | Definitions.Def_DetDLP_S8L_CycleSpec
-- name    : DetDLP_S8L_CycleSpec
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T20:28:52.829647+00:00
-- url     : https://prove2.me/theorems/ee370c98-6d36-4cf5-8693-e68e1b62a0f3
-- title:
--   Tag 5 CycleCode model and make_word specification
-- statement:
--   Proves base_spec, cycle_spec, and make_word for Tag 5 finite-field pair-collision queries.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8L_AtomModel
import Definitions.Def_DetDLP_S8L_StageOnly
import Definitions.Def_DetDLP_S8L_RangeOnly
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 1200000
namespace DetDLP.S8L.MakePacket
open S8H0 RegisterMap NamedBlocks GateSemantics S8H.PointAddresses S8C Groundwork M89S1 S8G.FpAtomRows
open DetDLP_W1_Queries OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
abbrev W := List Bool
abbrev pnum := FpPair.Packet.prime
abbrev bitsN (w : W) := S8G.FpMoment.Code.width (pnum w)
abbrev slots (w : W) := S8G.FpMoment.Code.slots (bitsN w)
abbrev wid (w : W) := bitsN w+1
abbrev pfx := FpPair.Packet.prefixBits
def raw (w : W) := base (slots w) (wid w) (wires (wid w)) (pfx w).length
def cyc (w : W) := CycleCode.code (raw w).1 (raw w).2
def make (w : List Bool) : List Bool := outerPacket w (S8H.WirePacket.packet ((cyc w).ng+(cyc w).nb) (cyc w).ne (cyc w).gate (fun j => (cyc w).ng+(cyc w).bit j)) (Bounds.packetScale (slots w) (bitsN w))
private theorem rep_spec {k : ℕ} {n : ℕ} (f : ℕ → NC) (u : Fin n → B (k+1)) (hc : ∀ i, (f i).1=(f 0).1) (hf : ∀ i : Fin n, Fits (f i) (u i)) : Fits (repeated n f) (Routes.allRows n u) := by
  apply many_spec; intro i; rw [← hc i]; exact hf i
private theorem atomC (m d e i : ℕ) : (atomN m d e i).1 = (atomN m d e 0).1 := by
  simp only [atomN, catN, prodN, colN, rangeN, rowN]
theorem base_spec (p m T X : ℕ) (cs : Fin m → ℕ × ℕ) (η : List Bool) :
  let n := Semantics.net p m T X cs η
  let u : B ((Semantics.shape p m).size+1) := ⟨⟨AnchoredLayout.anchors _,fun _ _ => true⟩,id⟩
  Fits (base m (Semantics.width p) (Routes.G (Semantics.width_pos p)) η.length) (joinB u n) := by
  dsimp only; unfold base Semantics.net Routes.network Routes.prefixRows
  refine cat_spec ⟨AnchoredLayout.anchorModels _,fun _ => rfl⟩ (cat_spec ⟨AnchoredLayout.anchorModels 1,fun _ => rfl⟩ (cat_spec ?_ (cat_spec ?_ (cat_spec ?_ (cat_spec ?_ ?_)))))
  · exact rep_spec _ _ (atomC _ _ _) (atom_spec _ _ _ _)
  · exact rep_spec _ _ (stageC _ _ _) (stage_spec _ _ _)
  · exact rep_spec _ _ (fun _ => rfl) (range_spec p)
  · apply row_spec; intro _ j; exact Fin.elim0 j
  · apply row_spec; intro i j; exact dig_spec p i
theorem cycle_spec (p m T X : ℕ) (cs : Fin m → ℕ × ℕ) (η : List Bool) :
  let b := base m (Semantics.width p) (Routes.G (Semantics.width_pos p)) η.length
  Models (CycleCode.code b.1 b.2) (Semantics.layout p m T X cs η) := by
  let b := base m (Semantics.width p) (Routes.G (Semantics.width_pos p)) η.length
  let n := Semantics.net p m T X cs η
  have M : Models b.1 (Semantics.core p m T X cs η).A := (base_spec p m T X cs η).1
  have N (i : Fin (Semantics.core p m T X cs η).A.ne) : b.2 i = (AnchoredLayout.signal n.core n.name i).val := (base_spec p m T X cs η).2 i
  have h := CycleCode.models M b.2
  have k := AnchoredLayout.next_congr (fun i : Fin (Semantics.core p m T X cs η).A.ne => b.2 i) (AnchoredLayout.signal n.core n.name) (by intro i j; rw [N,N]; exact Fin.val_inj)
  obtain ⟨_,he,hs,_⟩ := CycleCode.packetEndpoints M b.2
  have H : Models _ _ := ⟨h.ng,h.nb,he,hs,h.bit⟩; rw [k] at H; exact H
private theorem packet_model {c : Code} {A : w3_FactorLayout} (M : Models c A) : S8H.WirePacket.packet (c.ng+c.nb) c.ne c.gate (fun j => c.ng+c.bit j) = (w3_factorGraph A).subdivision.encode := by
  let G := w3_factorGraph A; have hv : c.ng+c.nb=G.nV := by rw [M.ng,M.nb]; rfl
  have he : c.ne=G.nE := M.ne; rw [hv,he]; exact S8H.WirePacket.packet_eq G _ _ (fun j => M.gate j) (fun j => by rw [M.ng,M.bit j]; rfl)
theorem make_word (p : ℕ) [Fact p.Prime] (T : ℕ) (S : FpSeed p (blockCount (bitLen p))) (X : (ZMod p)ˣ) (η : List Bool) : make (FpPair.word T S X η) = encodeBTNInstance (FpPair.word T S X η) (w3_factorGraph (Semantics.layout p (blockCount (bitLen p)) T (X : ZMod p).val (fun i => ((S i).1.val+1,(S i).2.val)) η)).subdivision (Bounds.packetScale (blockCount (bitLen p)) (bitLen p)) (Bounds.packetScale (blockCount (bitLen p)) (bitLen p)) 1 := by
  obtain ⟨hp,_,_,_,hf⟩ := FpPair.Packet.fields T S X η
  let w := FpPair.word T S X η
  have M : Models (cyc w) (Semantics.layout p (blockCount (bitLen p)) T (X : ZMod p).val (fun i => ((S i).1.val+1,(S i).2.val)) η) := by
    simpa only [cyc,raw,slots,wid,bitsN,pnum,pfx,w,hp,hf,S8G.FpMoment.Code.width_eq,S8G.FpMoment.Code.slots_eq,wires_eq (Semantics.width_pos p)] using cycle_spec p (blockCount (bitLen p)) T (X : ZMod p).val (fun i => ((S i).1.val+1,(S i).2.val)) η
  change outerPacket w _ _ = _; rw [packet_model M,outerPacket_eq]; simp only [slots,bitsN,pnum,w,hp,S8G.FpMoment.Code.width_eq,S8G.FpMoment.Code.slots_eq]
end DetDLP.S8L.MakePacket



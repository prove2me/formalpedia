-- Prove2me | Definitions.Def_DetDLP_S8L_MakePacket_v3
-- name    : DetDLP_S8L_MakePacket_v3
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T20:42:24.744262+00:00
-- url     : https://prove2.me/theorems/4765b49f-50c6-4eaa-bf91-b611cf2439ff
-- title:
--   Tag 5 uniform PolyT instance builder
-- statement:
--   Proves make_poly for Tag 5 finite-field pair-collision queries.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8L_SubPoly
import Definitions.Def_DetDLP_S8L_CycleSpec
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 1200000
namespace DetDLP.S8L.MakePacket
open S8H0 RegisterMap NamedBlocks GateSemantics S8H.PointAddresses S8C Groundwork M89S1 S8G.FpAtomRows
open DetDLP_W1_Queries OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
attribute [local fun_prop] PolyT.fst PolyT.snd PolyT.comp PolyT.prodMk PolyT.id' PolyT.const PolyT.mul PolyT.div PolyT.mod PolyT.length w4_M5Evaluator.clog2_poly w4_M5Evaluator.vertexCount_poly w4_M5EdgeNat.srcNat_poly w4_M5EdgeNat.dstNat_poly
attribute [local fun_prop] wiresP P2M_Groundwork_PolyT_ite__226169acf219 PolyT.decide_lt PolyT.decide_eq
private def pad (w : W) := (pnum w-1).bits ++ [false,false]
private def square (w : W) := (pad w).flatMap fun _ => pad w
private def big (w : W) := ((square w) ++ pfx w).flatMap (fun _ => List.replicate 1048576 ())
private theorem bound (w : W) : (cyc w).ng+(cyc w).nb+(cyc w).ne ≤ (big w).length ∧ (cyc w).ne+(cyc w).ne ≤ (big w).length := by
  let m := slots w; let p := pnum w; let d := wid w; let e := wires d; let l := (pfx w).length
  let z := base m d e 0
  let c := CycleCode.code z.1 z.2
  let cs : Fin m → ℕ × ℕ := fun _ => (0,0)
  have bm : m = blockCount (bitLen p) := by simp [m,slots,bitsN,p,S8G.FpMoment.Code.slots_eq,S8G.FpMoment.Code.width_eq]
  have hm : 1 ≤ m := bm ▸ (by exact (by decide : 1≤2).trans (le_max_left _ _))
  have M : Models c (Semantics.layout p m 0 0 cs []) := by simpa only [c,z,d,e,wid,bitsN,p,S8G.FpMoment.Code.width_eq,wires_eq (Semantics.width_pos _),List.length_nil] using cycle_spec p m 0 0 cs []
  have he := Bounds.edgeBudget p m 0 0 cs [] hm (by simp); have hg := Bounds.gateBudget p m 0 0 cs [] hm (by simp)
  rw [← M.ng] at hg; rw [← M.ne] at he
  have hs : FpPair.scale m (bitLen p) ≤ 524288*((bitLen p+2)*(bitLen p+2)) := by unfold FpPair.scale; rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (bm ▸ S8G.FpMoment.blockUpper _))
  have hb : (big w).length = (((bitLen p+2)*(bitLen p+2))+l)*1048576 := by
    have h : (pad w).length=bitLen p+2 := by simpa [pad,p,S8G.FpMoment.Code.width] using (S8G.FpMoment.Code.width_eq (pnum w))
    simp only [big,square,List.length_flatMap,List.length_replicate,List.map_const',List.sum_replicate_nat,List.length_append,Function.comp_def,h,l]
  have dn : (raw w).1.ne=z.1.ne+l := by simp only [raw,z,base,catN,sum,rowN,BaseCode.rowsCode,m,d,e,l,Nat.zero_mul,Nat.mul_one,Nat.add_zero]; omega
  have dg : (raw w).1.ng=z.1.ng+l := by simp only [raw,z,base,catN,sum,rowN,BaseCode.rowsCode,m,d,e,l,Nat.add_zero]; omega
  rw [hb,Nat.add_mul]; simp only [cyc,c,CycleCode.code] at he hg ⊢; rw [dn,dg]; constructor <;> omega
attribute [local fun_prop] FpPair.Packet.prime_poly FpPair.Packet.prefix_poly S8G.FpMoment.Code.width_poly S8G.FpMoment.Code.slots_poly
private theorem rawP {α : Type} [Enc α] {Wf : α → W} (h : PolyT Wf) : Eff (fun x => raw (Wf x)) := by
  apply baseP <;> simp only [slots,wid,bitsN,pnum,pfx] <;> fun_prop (disch := assumption)
theorem make_poly : Groundwork.PolyT make := by
  have B := rawP (α:=W) PolyT.id'
  have bp : PolyT pad := by unfold pad pnum; fun_prop
  have bs : PolyT square := PolyT.flatMap (PolyT.comp bp (PolyT.fst PolyT.id')) bp
  have hb : PolyT big := PolyT.flatMap (PolyT.const _) (PolyT.append bs FpPair.Packet.prefix_poly)
  have U {q : W → ℕ} (hq : PolyT q) (hl : ∀ w, q w ≤ (big w).length) : Unary q := (PolyT.unary_min_length hq hb).congr fun w => by simp only [min_eq_left (hl w)]
  have hV := PolyT.add (PolyT.add B.1 B.2.1) B.2.1; have hE := PolyT.add B.2.1 (PolyT.add B.2.1 B.2.1)
  have g := (rawP (PolyT.fst (PolyT.id' (α:=W × ℕ)))).2.2 (PolyT.snd PolyT.id')
  have c := CycleCode.endpoints_poly (c:=fun w => (raw w).1) (name:=fun w => (raw w).2) B.1 B.2.1 (U B.2.1 (fun w => le_trans (show (raw w).1.ne ≤ (cyc w).ne+(cyc w).ne by simp [cyc,CycleCode.code]; omega) (bound w).2)) g.1 g.2
  exact outerPacket_poly PolyT.id' (S8H.WirePacket.packet_poly (nv:=fun w => (cyc w).ng+(cyc w).nb) (ne:=fun w => (cyc w).ne) (src:=fun w => (cyc w).gate) (dst:=fun w j => (cyc w).ng+(cyc w).bit j) hV hE (U (PolyT.add hV hE) (fun w => (bound w).1)) (U (PolyT.add hE hE) (fun w => (bound w).2)) c.1 (PolyT.add (PolyT.comp (f:=fun w : W => (cyc w).ng) (g:=Prod.fst (β:=ℕ)) (PolyT.add B.1 B.2.1) (PolyT.fst PolyT.id')) c.2)) (by unfold Bounds.packetScale slots bitsN pnum; fun_prop)
end DetDLP.S8L.MakePacket



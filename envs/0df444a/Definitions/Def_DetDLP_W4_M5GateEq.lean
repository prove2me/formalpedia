-- Prove2me | Definitions.Def_DetDLP_W4_M5GateEq
-- name    : DetDLP_W4_M5GateEq
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T04:33:39.672074+00:00
-- url     : https://prove2.me/theorems/2c0173ef-ea41-4085-9ab3-861afe7098fb
-- title:
--   Agreement of the indexed evaluator with every tensor gate
-- statement:
--   At each vertex the padded arithmetic evaluator returns exactly the local Boolean tensor predicate on the bits read from its incident ports.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3, Lemma 2.3 (pp. 8–9)

import Definitions.Def_DetDLP_W4_M5GateValues
set_option autoImplicit false
namespace DetDLP.w4_M5GateEq
open w4_MulParams w4_M5GraphBounds w4_M5GateOps w4_M5GateNat w4_M5TranscriptBridge w4_M5PortTensor w4_ConvolutionArithmetic
variable (q : Pad)
variable (hd : 1 ≤ q.length) (v : Fin (vertexCount q.length)) (a : List Bool)
include hd
set_option linter.unusedSimpArgs false
open w4_M5GateValues
set_option maxHeartbeats 1800000
attribute [local irreducible] w1 w2 w3 w4 w5 w6 w7 w8 inDigit outDigit linkL linkR Q w4_M5GateNat.first w4_M5GateNat.second w4_M5GateNat.third w4_M5GateNat.fourth unpack readWire
private theorem check_pack (t : Fin (2)) (u : Fin (n0 q.length)) : w4_M5Dispatch.gate ((q,v.val,a) : Ctx) (.pack t u) = node (.pack t u) (readWire hd v (fun i => a[i.val]?.getD false)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [w4_M5Dispatch.gate,dim,pad,Prod.fst,Prod.snd,w4_M5GateNat.pack,node,packCheck,decide_eq_true_eq,eq1 q hd v a t u,inD q hd v a,packedGate]; refine Iff.trans ?_ ⟨fun h => decide_eq_true h, fun h => of_decide_eq_true h⟩; exact wordResidue q hd _ _ _ rfl
private theorem check_forward1 (t : Fin (2)) (b : Fin (L2 q.length)) : w4_M5Dispatch.gate ((q,v.val,a) : Ctx) (.forward1 t b) = node (.forward1 t b) (readWire hd v (fun i => a[i.val]?.getD false)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [w4_M5Dispatch.gate,dim,pad,Prod.fst,Prod.snd,forward1,node,forward1Check,decide_eq_true_eq,allN_true q (bounds q hd).2.2.1]; apply forall_congr'; intro i
  rw [eq2 q hd v a t b i,firstGate]; exact wordResidue q hd _ _ _ (firstCast q hd v a t i b)
private theorem check_forward2 (t : Fin (2)) (i : Fin (L1 q.length)) : w4_M5Dispatch.gate ((q,v.val,a) : Ctx) (.forward2 t i) = node (.forward2 t i) (readWire hd v (fun i => a[i.val]?.getD false)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [w4_M5Dispatch.gate,dim,pad,Prod.fst,Prod.snd,forward2,node,forward2Check,decide_eq_true_eq,allN_true q (bounds q hd).2.2.2.1]; apply forall_congr'; intro b
  rw [eq3 q hd v a t b i,secondGate]; exact wordResidue q hd _ _ _ (secondCast q hd v a t i b)
private theorem check_pointwise (b : Fin (L2 q.length)) (i : Fin (L1 q.length)) : w4_M5Dispatch.gate ((q,v.val,a) : Ctx) (.pointwise b i) = node (.pointwise b i) (readWire hd v (fun i => a[i.val]?.getD false)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [w4_M5Dispatch.gate,dim,pad,Prod.fst,Prod.snd,pointwise,node,pointCheck,decide_eq_true_eq,eq4 q hd v a b i,pointGate]; refine Iff.trans ?_ ⟨fun h => decide_eq_true h, fun h => of_decide_eq_true h⟩; apply wordResidue q hd
  have h0 := eq3 q hd v a 0 b i
  have h1 := eq3 q hd v a 1 b i
  simp only [Fin.val_zero,Fin.val_one] at h0 h1
  rw [Nat.cast_mul,h0,h1]; rfl
private theorem check_inverse1 (i : Fin (L1 q.length)) : w4_M5Dispatch.gate ((q,v.val,a) : Ctx) (.inverse1 i) = node (.inverse1 i) (readWire hd v (fun i => a[i.val]?.getD false)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [w4_M5Dispatch.gate,dim,pad,Prod.fst,Prod.snd,inverse1,node,inverse1Check,decide_eq_true_eq,allN_true q (bounds q hd).2.2.2.1]; apply forall_congr'; intro b
  rw [eq5 q hd v a b i,thirdGate]; exact wordResidue q hd _ _ _ (thirdCast q hd v a i b)
private theorem check_inverse2 (b : Fin (L2 q.length)) : w4_M5Dispatch.gate ((q,v.val,a) : Ctx) (.inverse2 b) = node (.inverse2 b) (readWire hd v (fun i => a[i.val]?.getD false)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [w4_M5Dispatch.gate,dim,pad,Prod.fst,Prod.snd,inverse2,node,inverse2Check,decide_eq_true_eq,allN_true q (bounds q hd).2.2.2.2.1]; apply forall_congr'; intro u
  by_cases h : u.val % L2 q.length = b.val
  · simp only [dim,h,if_true,true_implies,decide_eq_true_eq,eq6 q hd v a u,coeffGate]; exact wordResidue q hd _ _ _ (by simpa only [h] using fourthCast q hd v a u)
  · simp [dim,h]
private theorem check_carry (u : Fin (2*n0 q.length)) : w4_M5Dispatch.gate ((q,v.val,a) : Ctx) (.carry u) = node (.carry u) (readWire hd v (fun i => a[i.val]?.getD false)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [w4_M5Dispatch.gate,dim,pad,Prod.fst,Prod.snd,w4_M5GateNat.carry,node,carryCheck,decide_eq_true_eq,eq6 q hd v a u,linkLeft q hd v a,linkRight q hd v a,outD q hd v a,pow2,cap,dim,pad,min_eq_left (bounds q hd).2.1,base]
private theorem check_carrySpacer (u : Fin (2*n0 q.length-1)) : w4_M5Dispatch.gate ((q,v.val,a) : Ctx) (.carrySpacer u) = node (.carrySpacer u) (readWire hd v (fun i => a[i.val]?.getD false)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [w4_M5Dispatch.gate,dim,pad,Prod.fst,Prod.snd,carrySpacer,node,spacerCheck,decide_eq_true_eq,eq7 q hd v a u,eq8 q hd v a u,(bitsToNat_injective _).eq_iff]
theorem gate_eq (u : Vertex q.length) : w4_M5Dispatch.gate ((q,v.val,a) : Ctx) u = node u (readWire hd v (fun i => a[i.val]?.getD false)) := by
  cases u with
  | inputBit | outputBit => rfl
  | pack t u => exact check_pack q hd v a t u
  | forward1 t b => exact check_forward1 q hd v a t b
  | forward2 t i => exact check_forward2 q hd v a t i
  | pointwise b i => exact check_pointwise q hd v a b i
  | inverse1 i => exact check_inverse1 q hd v a i
  | inverse2 b => exact check_inverse2 q hd v a b
  | carry u => exact check_carry q hd v a u
  | carrySpacer u => exact check_carrySpacer q hd v a u
end DetDLP.w4_M5GateEq



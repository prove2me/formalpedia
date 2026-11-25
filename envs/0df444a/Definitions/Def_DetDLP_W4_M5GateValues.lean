-- Prove2me | Definitions.Def_DetDLP_W4_M5GateValues
-- name    : DetDLP_W4_M5GateValues
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T04:19:40.865043+00:00
-- url     : https://prove2.me/theorems/1796fe53-38f2-4216-b91f-3723bc7cbca7
-- title:
--   Fermat gate values in the padded word evaluator
-- statement:
--   The natural-number arithmetic on a unary-padded dimension computes the canonical word values, forward and inverse transform residues, and carry-link values read from the incident ports.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3, Lemma 2.3 (pp. 8–9)

import Definitions.Def_DetDLP_W4_M5Dispatch
set_option autoImplicit false
namespace DetDLP.w4_M5GateValues
open w4_MulParams w4_M5GraphBounds w4_M5GateOps w4_M5GateNat w4_M5TranscriptBridge w4_M5PortTensor w4_ConvolutionArithmetic
variable (q : Pad)
variable (hd : 1 ≤ q.length) (v : Fin (vertexCount q.length)) (a : List Bool)
include hd
set_option linter.unusedSimpArgs false
theorem bounds : W q.length ≤ 1100*(q.length+1) ∧ k q.length ≤ 1100*(q.length+1) ∧ L1 q.length ≤ 1100*(q.length+1) ∧ L2 q.length ≤ 1100*(q.length+1) ∧ 2*n0 q.length ≤ 1100*(q.length+1) ∧ 2*J q.length ≤ 1100*(q.length+1) := by
  have := J_lt_linear hd; have := L_lower hd; have := (size_bounds hd).1; have := L1_le_L q.length; have := L2_le_L q.length; unfold W k; omega
theorem qval : Q q = modulus q.length := by have := (bounds q hd).2.2.2.2.2; simp [Q,pow2,cap,min_eq_left (show J q.length ≤ 1100*(q.length+1) by omega)]
theorem root (n : ℕ) : (rootPow q n : FermatRing q.length) = w4_MulParams.omega q.length ^ n := by
  have h := Nat.mod_lt (rootStep q.length*n) (show 0 < 2*J q.length by have := J_ge_sixteen hd; omega)
  have := (bounds q hd).2.2.2.2.2
  simp only [rootPow,pow2,cap,min_eq_left (show (rootStep q.length*n)%(2*J q.length) ≤ 1100*(q.length+1) by omega),Nat.cast_pow,Nat.cast_ofNat,w4_MulParams.omega,← pow_mul]
  apply (pow_eq_pow_mod _ _).symm
  rw [two_mul,pow_add]; change (2 : FermatRing q.length)^J q.length * 2^J q.length = 1; rw [two_pow_J hd]; ring
theorem inv (n : ℕ) : (invPow q n : FermatRing q.length) = wInv q.length ^ n := by rw [invPow,root q hd,wInv,pow_mul]
theorem scale : (invScale q : FermatRing q.length) = inverseL q.length := by
  have := (bounds q hd).2.2.2.2.2
  have h := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.sub_le (J q.length) (μ q.length))
  rw [invScale,qval q hd,pow2,cap,min_eq_left (by omega),Nat.cast_sub (by unfold modulus; omega)]
  simp only [modulus,ZMod.natCast_self,Nat.cast_pow,Nat.cast_ofNat,zero_sub,inverseL]
theorem eq1 (t : Fin 2) (i : Fin (n0 q.length)) : w1 ((q,v.val,a) : Ctx) t i = bitsToNat ((unpack (readWire hd v (fun i => a[i.val]?.getD false))).packed (flag t) i) := by
  simp only [w1,pad,dim,Prod.fst,Prod.snd]; rw [word_eq q (bounds q hd).1]; apply congrArg bitsToNat; funext z
  simp only [unpack,tag_flag]; exact wire_eq q hd v a (.packForward t i z)
theorem eq2 (t : Fin 2) (b : Fin (L2 q.length)) (i : Fin (L1 q.length)) : w2 ((q,v.val,a) : Ctx) t b i = bitsToNat ((unpack (readWire hd v (fun i => a[i.val]?.getD false))).forwardMiddle (flag t) i b) := by
  simp only [w2,pad,dim,Prod.fst,Prod.snd]; rw [word_eq q (bounds q hd).1]; apply congrArg bitsToNat; funext z
  simp only [unpack,tag_flag]; exact wire_eq q hd v a (.forwardMiddle t b i z)
theorem eq3 (t : Fin 2) (b : Fin (L2 q.length)) (i : Fin (L1 q.length)) : w3 ((q,v.val,a) : Ctx) t b i = bitsToNat ((unpack (readWire hd v (fun i => a[i.val]?.getD false))).forwardPoint (flag t) i b) := by
  simp only [w3,pad,dim,Prod.fst,Prod.snd]; rw [word_eq q (bounds q hd).1]; apply congrArg bitsToNat; funext z
  simp only [unpack,tag_flag]; exact wire_eq q hd v a (.forwardPoint t b i z)
theorem eq4 (b : Fin (L2 q.length)) (i : Fin (L1 q.length)) : w4 ((q,v.val,a) : Ctx) b i = bitsToNat ((unpack (readWire hd v (fun i => a[i.val]?.getD false))).pointInverse i b) := by
  simp only [w4,pad,dim,Prod.fst,Prod.snd]; rw [word_eq q (bounds q hd).1]; apply congrArg bitsToNat; funext z
  simp only [unpack,tag_flag]; exact wire_eq q hd v a (.pointInverse b i z)
theorem eq5 (b : Fin (L2 q.length)) (i : Fin (L1 q.length)) : w5 ((q,v.val,a) : Ctx) b i = bitsToNat ((unpack (readWire hd v (fun i => a[i.val]?.getD false))).inverseMiddle i b) := by
  simp only [w5,pad,dim,Prod.fst,Prod.snd]; rw [word_eq q (bounds q hd).1]; apply congrArg bitsToNat; funext z
  simp only [unpack,tag_flag]; exact wire_eq q hd v a (.inverseMiddle b i z)
theorem eq6 (u : Fin (2*n0 q.length)) : w6 ((q,v.val,a) : Ctx) u = bitsToNat ((unpack (readWire hd v (fun i => a[i.val]?.getD false))).coefficient u) := by
  simp only [w6,pad,dim,Prod.fst,Prod.snd]; rw [word_eq q (bounds q hd).1]; apply congrArg bitsToNat; funext z
  simp only [unpack,tag_flag]; exact wire_eq q hd v a (.coefficient u z)
theorem eq7 (u : Fin (2*n0 q.length-1)) : w7 ((q,v.val,a) : Ctx) u = bitsToNat ((unpack (readWire hd v (fun i => a[i.val]?.getD false))).carryLeft u) := by
  simp only [w7,pad,dim,Prod.fst,Prod.snd]; rw [word_eq q (bounds q hd).1]; apply congrArg bitsToNat; funext z
  simp only [unpack,tag_flag]; exact wire_eq q hd v a (.carryLeft u z)
theorem eq8 (u : Fin (2*n0 q.length-1)) : w8 ((q,v.val,a) : Ctx) u = bitsToNat ((unpack (readWire hd v (fun i => a[i.val]?.getD false))).carryRight u) := by
  simp only [w8,pad,dim,Prod.fst,Prod.snd]; rw [word_eq q (bounds q hd).1]; apply congrArg bitsToNat; funext z
  simp only [unpack,tag_flag]; exact wire_eq q hd v a (.carryRight u z)
theorem inD (t : Fin 2) (u : ℕ) : inDigit ((q,v.val,a) : Ctx) t u = inputDigit (fun i => (readWire hd v (fun i => a[i.val]?.getD false)) (extEdge i)) (flag t) u := by
  simp only [inDigit,pad,dim,Prod.fst,Prod.snd]; rw [word_eq q (bounds q hd).2.1]; apply congrArg bitsToNat; funext i
  simp only [bitWindow,dim]; split <;> rename_i h
  · rw [operand_ext,tag_flag]; exact wire_eq q hd v a (.input t ⟨_,h⟩)
  · rfl
theorem outD (u : ℕ) : outDigit ((q,v.val,a) : Ctx) u = outputDigit (fun i => (readWire hd v (fun i => a[i.val]?.getD false)) (extEdge i)) u := by
  simp only [outDigit,pad,dim,Prod.fst,Prod.snd]; rw [word_eq q (bounds q hd).2.1]; apply congrArg bitsToNat; funext i
  simp only [bitWindow,dim]; split <;> rename_i h
  · rw [output_ext]; exact wire_eq q hd v a (.output ⟨_,h⟩)
  · rfl
omit hd in
theorem sumCast {n : ℕ} (hn : n ≤ 1100*(q.length+1)) (f : ℕ → ℕ) (g : ℕ → FermatRing q.length) (hh : ∀ j : Fin n, (f j : FermatRing q.length) = g j) : (sumN q n f : FermatRing q.length) = ∑ j ∈ Finset.range n, g j := by
  rw [sumN_eq q hn,Nat.cast_sum,← Fin.sum_univ_eq_sum_range]; exact Finset.sum_congr rfl (fun j _ => hh j)
theorem pCast (t : Fin 2) (n : ℕ) : (packed ((q,v.val,a) : Ctx) t n : FermatRing q.length) = readPacked (d := q.length) ((unpack (readWire hd v (fun i => a[i.val]?.getD false))).packed (flag t)) n := by
  by_cases h : n < n0 q.length
  · simp only [packed,dim,if_pos h,readPacked,dif_pos h,decode]; rw [eq1 q hd v a t ⟨n,h⟩]
  · simp [packed,dim,readPacked,h]
theorem firstCast (t : Fin 2) (i : Fin (L1 q.length)) (b : Fin (L2 q.length)) : (w4_M5GateNat.first ((q,v.val,a) : Ctx) t i b : FermatRing q.length) = fwd1 (L1 q.length) (L2 q.length) (w4_MulParams.omega q.length) (readPacked (d := q.length) ((unpack (readWire hd v (fun i => a[i.val]?.getD false))).packed (flag t))) i b := by
  simp only [w4_M5GateNat.first,pad,dim,Nat.cast_mul,root q hd,fwd1]; congr 1
  apply sumCast q (bounds q hd).2.2.1; intro j; rw [Nat.cast_mul,root q hd,pCast]
theorem secondCast (t : Fin 2) (i : Fin (L1 q.length)) (b : Fin (L2 q.length)) : (w4_M5GateNat.second ((q,v.val,a) : Ctx) t i b : FermatRing q.length) = fwd2 (L1 q.length) (L2 q.length) (w4_MulParams.omega q.length) (readGrid (d := q.length) ((unpack (readWire hd v (fun i => a[i.val]?.getD false))).forwardMiddle (flag t))) i b := by
  unfold w4_M5GateNat.second fwd2; apply sumCast q (bounds q hd).2.2.2.1; intro j
  rw [Nat.cast_mul,root q hd,readGrid,dif_pos i.isLt,dif_pos j.isLt,decode,eq2 q hd v a t j i]
theorem thirdCast (i : Fin (L1 q.length)) (b : Fin (L2 q.length)) : (w4_M5GateNat.third ((q,v.val,a) : Ctx) i b : FermatRing q.length) = inv1 (L1 q.length) (L2 q.length) (wInv q.length) (readGrid (d := q.length) (unpack (readWire hd v (fun i => a[i.val]?.getD false))).pointInverse) i b := by
  unfold w4_M5GateNat.third inv1; apply sumCast q (bounds q hd).2.2.2.1; intro j
  rw [Nat.cast_mul,inv q hd,readGrid,dif_pos i.isLt,dif_pos j.isLt,decode,eq4 q hd v a j i]
theorem fourthCast (u : Fin (ncoef q.length)) : (w4_M5GateNat.fourth ((q,v.val,a) : Ctx) u : FermatRing q.length) = inv2 (L1 q.length) (L2 q.length) (wInv q.length) (inverseL q.length) (readGrid (d := q.length) (unpack (readWire hd v (fun i => a[i.val]?.getD false))).inverseMiddle) (u.val/L2 q.length) (u.val%L2 q.length) := by
  simp only [w4_M5GateNat.fourth,dim,pad,Nat.cast_mul,scale q hd,inv2]; congr 1
  apply sumCast q (bounds q hd).2.2.1; intro j
  have h := Nat.mod_lt u.val (L2_pos q.length)
  rw [Nat.cast_mul,inv q hd,readGrid,dif_pos j.isLt,dif_pos h,decode,eq5 q hd v a ⟨_,h⟩ j]
theorem wordResidue (w : Word q.length) (r : FermatRing q.length) (n : ℕ) (h : (n : FermatRing q.length) = r) : (bitsToNat w = n % Q q) ↔ w = encode q.length r := by
  rw [← (bitsToNat_injective _).eq_iff,bits_encode,← h,ZMod.val_natCast,qval q hd]
theorem linkLeft (j : ℕ) : linkL ((q,v.val,a) : Ctx) j = atLink (d := q.length) (unpack (readWire hd v (fun i => a[i.val]?.getD false))).carryLeft j := by
  by_cases h : 0 < j <;> by_cases h' : j < 2*n0 q.length <;> simp only [linkL,dim,atLink,ncoef,h,h',and_self,if_true,if_false,dite_true,dite_false,false_and,and_false]
  exact eq7 q hd v a ⟨j-1,by omega⟩
theorem linkRight (j : ℕ) : linkR ((q,v.val,a) : Ctx) j = atLink (d := q.length) (unpack (readWire hd v (fun i => a[i.val]?.getD false))).carryRight j := by
  by_cases h : 0 < j <;> by_cases h' : j < 2*n0 q.length <;> simp only [linkR,dim,atLink,ncoef,h,h',and_self,if_true,if_false,dite_true,dite_false,false_and,and_false]
  exact eq8 q hd v a ⟨j-1,by omega⟩
end DetDLP.w4_M5GateValues



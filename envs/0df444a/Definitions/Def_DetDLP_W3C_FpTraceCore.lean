-- Prove2me | Definitions.Def_DetDLP_W3C_FpTraceCore
-- name    : DetDLP_W3C_FpTraceCore
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T23:17:00.74006+00:00
-- url     : https://prove2.me/theorems/f6ba7364-ce40-4587-ab4b-cad198b1b80a
-- title:
--   Finite-field trace encoding helpers
-- statement:
--   Polynomial-time finite-field trace encoding, row packet, and tuple-word helpers used by the Stage-II trace controller.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_W3C_FpStep
import Definitions.Def_DetDLP_W3C_Stage2Trace
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 900000
namespace DetDLP.W3C.FpTraceStep
open Groundwork DetDLP_W1_Queries FpStep BlockLookup NineOracleLoop NewtonPoly OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
attribute [local fun_prop] PolyT.comp PolyT.fst PolyT.snd PolyT.prodMk PolyT.id' PolyT.const PolyT.flatMap PolyT.map PolyT.length PolyT.flatten
  PolyT.beq' PolyT.cond' PolyT.add PolyT.mod PolyT.mul PolyT.sub PolyT.div PolyT.decide_eq PolyT.decide_lt PolyT.decide_le w5_M6Sort.cw_poly w5_M6Sort.encode_poly frame_poly
  S8G.FpMoment.Code.width_poly P2M_Groundwork_PolyT_cons__3a60f43a3b86 P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_ite__226169acf219
variable {α β : Type} [Enc α] [Enc β]
@[local fun_prop] private theorem encP (e : β → W) (he : PolyT e) {l : α → List β} (hl : PolyT l) : PolyT fun x => Encoding.encodeList e (l x) := by
  have flat (v : List β) : Encoding.encodeList e v = v.flatMap (fun a => true :: frame (e a)) ++ [false] := by induction v with | nil => rfl | cons a v ih => simp [Encoding.encodeList,ih,List.flatMap,List.append_assoc]
  simp only [flat]; fun_prop
def inds (xs : List β) := List.range xs.length
@[fun_prop] theorem indsP {l : α → List β} (hl : PolyT l) : PolyT fun x => inds (l x) := PolyT.range (Unary.of_length hl)
def coords (b : Blocks) := inds ([] :: [] :: b.flatten)
def fullRep (r : List ℕ) := Encoding.encodeList id [encodeNatListBin (r.map fun _ => 0),
  Encoding.encodeList encodeIntBin (r.flatMap fun i => r.map fun j => if i=j then (1:ℤ) else 0)]
@[fun_prop] theorem fullP {r : α → List ℕ} (h : PolyT r) : PolyT fun x => fullRep (r x) := by
  have hI : PolyT encodeIntBin := P2M_Groundwork_PolyT_cons__3a60f43a3b86 (PolyT.sgn' PolyT.id') (w5_M6Sort.cw_poly (PolyT.natAbs PolyT.id'))
  unfold fullRep; fun_prop
theorem native_blocks {p m : ℕ} [NeZero p] (B : Fin m → List (ZMod p)ˣ) : decodeBlocks (encodeFpFactorBlocks B) =
    List.ofFn (fun i => (B i).map fun u : (ZMod p)ˣ => countWord (u : ZMod p).val) := by rw [encodeFpFactorBlocks,decodeBlocks_correct,List.map_ofFn]; rfl
theorem fullRep_correct (N : ℕ) : fullRep (List.range N) = encodeCosetRep (fun _ : Fin N => 0) (1 : Matrix (Fin N) (Fin N) ℤ) := by
  rw [fullRep,← List.map_coe_finRange N]; simp [encodeCosetRep,List.ofFn_eq_map,List.flatMap_map,List.map_map,Function.comp_def,Matrix.one_apply,Fin.ext_iff,-List.map_coe_finRange_eq_range]
def residue (M : ℕ) (z : ℤ) := (z.toNat + (M - (-z).toNat % M)) % M
theorem residue_eq (M : ℕ) [NeZero M] (z : ℤ) : residue M z = (z : ZMod M).val := by
  rw [residue,← ZMod.val_natCast]; congr 1
  rw [Nat.cast_add,Nat.cast_sub (Nat.mod_lt _ (NeZero.pos M)).le,ZMod.natCast_self,ZMod.natCast_mod]
  have h : (z.toNat : ℤ) - ((-z).toNat : ℤ) = z := by omega
  calc _ = (((z.toNat : ℤ) - ((-z).toNat : ℤ) : ℤ) : ZMod M) := by push_cast; ring
       _ = _ := congrArg _ h
def rowPkt (M rhs : ℕ) (r : List ℤ) := Encoding.encodeList id [encodeNatListBin (r.map (residue M)),countWord rhs]
@[fun_prop] theorem rowP {m k : α → ℕ} {r : α → List ℤ} (hm : PolyT m) (hk : PolyT k) (hr : PolyT r) :
    PolyT fun x => rowPkt (m x) (k x) (r x) := by unfold rowPkt residue; fun_prop
/-- Separator tuples, unlike seed plans, have little-endian fixed-width coordinates. -/
def tupleWords (b : ℕ) (u : W) := ((inds u).take (u.length/b)).map fun i => countWord (PolyT.bval ((u.drop (i*b)).take b))
@[fun_prop] theorem tupleP {b : α → ℕ} {u : α → W} (hb : PolyT b) (hu : PolyT u) :
    PolyT fun x => tupleWords (b x) (u x) := by unfold tupleWords; fun_prop
theorem tupleWords_correct (b : ℕ) (hb : 0<b) (ns : List ℕ) (fits : ∀ n ∈ ns, n < 2^b) :
    tupleWords b (ns.flatMap (w3_bits b)) = ns.map countWord := by
  have val (k n : ℕ) (hn : n < 2^k) : PolyT.bval (w3_bits k n) = n := by
    induction k generalizing n with
    | zero => have hn0 := (show n = 0 by simpa using hn); subst n; rfl
    | succ k ih => unfold w3_bits; rw [List.ofFn_succ,PolyT.bval_cons]; simp only [Fin.val_zero,Fin.val_succ,Nat.testBit_succ]
                   change 2 * PolyT.bval (w3_bits k (n/2)) + _ = n
                   rw [ih _ ((Nat.div_lt_iff_lt_mul (by decide)).2 (by simpa [pow_succ] using hn)),Nat.testBit_zero]; by_cases h : n%2=1 <;> simp [h] <;> omega
  have slice (l : List ℕ) (i : ℕ) (hi : i<l.length) : (((l.flatMap (w3_bits b)).drop (i*b)).take b) = w3_bits b l[i] := by
    induction l generalizing i with
    | nil => simp at hi
    | cons a l ih => have len : (w3_bits b a).length = b := by simp [w3_bits]
                     cases i with
                     | zero => simpa only [List.flatMap_cons,Nat.zero_mul,List.drop_zero,List.getElem_cons_zero,len] using (List.take_left (l₁:=w3_bits b a) (l₂:=l.flatMap (w3_bits b)))
                     | succ i => simp only [List.flatMap_cons,Nat.succ_mul,List.drop_append,len,List.getElem_cons_succ]
                                 rw [List.drop_eq_nil_of_le (show (w3_bits b a).length ≤ i*b+b by rw [len]; omega)]; simpa using ih i (by simpa using hi)
  have len : (ns.flatMap (w3_bits b)).length = ns.length*b := by induction ns with | nil => simp | cons a l ih => simp_all [List.flatMap_cons,w3_bits,Nat.succ_mul,Nat.add_comm]
  unfold tupleWords inds; rw [List.take_range,len,Nat.mul_div_cancel _ hb,Nat.min_eq_left (Nat.le_mul_of_pos_right _ hb)]
  apply List.ext_getElem <;> simp only [List.length_map,List.length_range,List.getElem_map,List.getElem_range]
  intro i h _; exact congrArg countWord ((congrArg PolyT.bval (slice ns i h)).trans (val _ _ (fits _ (List.getElem_mem ..))))
def positive (M : ℕ) (pkt ans : W) := let f := decodeFrames pkt
  massPosWord (PolyT.bval (f.getD 3 [])) M (PolyT.bval (f.getD 6 [])) ans
theorem positive_spec {q : w3_Query} {C : ℕ} (n : w3_Net q C) {v : W}
    (hv : EncodesTruncPoly (w3_precision q) (w3_len q) v (BTNContract n.G n.T)) :
    positive q.M (w3_packet n) v = decide (0 < w3_mass q) := by simpa [positive,w3_packet,encodeTerminalBTNInstance] using massPosWord_correct n hv
attribute [local irreducible] decodeFrames decodeBlocks S8G.FpMoment.Code.width w5_M6Sort.decode massPosWord PolyT.bval

end DetDLP.W3C.FpTraceStep



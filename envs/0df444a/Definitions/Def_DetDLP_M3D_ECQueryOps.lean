-- Prove2me | Definitions.Def_DetDLP_M3D_ECQueryOps
-- name    : DetDLP_M3D_ECQueryOps
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T13:19:03.174942+00:00
-- url     : https://prove2.me/theorems/ba67d81c-69d9-4e9c-8a77-a2c731878f9f
-- title:
--   EC controller query operations
-- statement:
--   Polynomial-time EC query adapters and exact coordinate and tuple-prefix semantics for the nine-oracle stage-two controller.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_M3D_ECQueries

set_option autoImplicit false
namespace DetDLP.M3D.ECQueryOps
open Groundwork M3D.ECQueries W3C.BlockLookup
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
abbrev W := List Bool

def elemWord (inp : W) (bs : Blocks) (j : ℕ) : W :=
  if j < bs.flatten.length then bs.flatten.getD j [] else
  encodeNatListBin (if j = bs.flatten.length then firstPointCoords inp else secondPointCoords inp)

def unitGenRow (bs : Blocks) : List ℕ :=
  (List.range ([] :: [] :: bs.flatten).length).map fun j => if j = bs.flatten.length then 1 else 0

def planWord (ans : W) := (decodeFrames ans).getD 1 []
def threshold (ans : W) := PolyT.bval ((decodeFrames (planWord ans).tail).getD 0 [])
def seedBits (ans : W) := (decodeFrames (planWord ans).tail).getD 1 []

variable {α : Type} [Enc α]
attribute [local fun_prop] PolyT.comp PolyT.const PolyT.fst PolyT.snd PolyT.map PolyT.length
  PolyT.getD PolyT.take PolyT.drop PolyT.tail PolyT.bval' PolyT.reverse PolyT.mul PolyT.flatten
  PolyT.decide_eq PolyT.decide_lt P2M_Groundwork_PolyT_ite__226169acf219
  P2M_Groundwork_PolyT_cons__3a60f43a3b86 P2M_Groundwork_PolyT_id__1c5d0f44cc8f
  w5_M6Sort.encode_poly PolyT.flatMap PolyT.prodMk

@[fun_prop] theorem elemWord_poly {w : α → W} {bs : α → Blocks} {j : α → ℕ}
    (hw : PolyT w) (hb : PolyT bs) (hj : PolyT j) : PolyT fun x => elemWord (w x) (bs x) (j x) := by
  unfold elemWord; fun_prop

private def inds {β : Type} (xs : List β) := List.range xs.length
@[local fun_prop] private theorem indsP {β : Type} [Enc β] {xs : α → List β} (h : PolyT xs) :
    PolyT fun x => inds (xs x) := PolyT.range (Unary.of_length h)

@[fun_prop] theorem unitGenRow_poly {bs : α → Blocks} (hb : PolyT bs) : PolyT fun x => unitGenRow (bs x) := by
  unfold unitGenRow; change PolyT (fun x => (inds ([] :: [] :: (bs x).flatten)).map _); fun_prop

@[fun_prop] theorem planWord_poly {w : α → W} (hw : PolyT w) : PolyT fun x => planWord (w x) := by unfold planWord; fun_prop
@[fun_prop] theorem threshold_poly {w : α → W} (hw : PolyT w) : PolyT fun x => threshold (w x) := by unfold threshold; fun_prop
@[fun_prop] theorem seedBits_poly {w : α → W} (hw : PolyT w) : PolyT fun x => seedBits (w x) := by unfold seedBits; fun_prop

variable {p m : ℕ} [NeZero p] {E : WeierstrassCurve (ZMod p)}
local notation "encP" => (fun A : E.toAffine.Point => encodeNatListBin (pointCoords A))

private theorem flat_eq (FB : IndexedFactorBase E.toAffine.Point m) :
    (blocks FB encP).flatten = ((List.finRange m).flatMap FB.blocks).map encP := by
  simp [blocks,List.ofFn_eq_map,List.flatMap_def,List.map_flatten,List.map_map,Function.comp_def]

private theorem baseLen (FB : IndexedFactorBase E.toAffine.Point m) :
    (blocks FB encP).flatten.length = FB.totalBaseSize := by
  rw [flat_eq,List.length_map,List.length_flatMap]; exact (Fin.sum_univ_def _).symm

theorem elemWord_correct (FB : IndexedFactorBase E.toAffine.Point m) (P Q : E.toAffine.Point)
    (j : Fin FB.totalCoords) : elemWord (encodeECDLPInput p E P Q) (blocks FB encP) j = encP (FB.elem P Q j) := by
  simp only [elemWord,baseLen,IndexedFactorBase.elem]; split_ifs with h h'
  · have hh : j.val < (blocks FB encP).flatten.length := (baseLen FB).symm ▸ h
    rw [flat_eq] at hh ⊢; rw [List.getD_eq_getElem _ _ hh]
    simp
  all_goals cases P <;> cases Q <;> simp [firstPointCoords,secondPointCoords,inputFields,encodeECDLPInput,pointCoords]

theorem unitGenRow_correct (FB : IndexedFactorBase E.toAffine.Point m) :
    unitGenRow (blocks FB encP) = List.ofFn (fun j : Fin FB.totalCoords => if j = FB.genCoord then 1 else 0) := by
  apply List.ext_getElem
  · simp only [unitGenRow,List.length_map,List.length_range,List.length_cons,List.length_ofFn,baseLen]; rfl
  · intro i h k; simp only [unitGenRow,List.getElem_map,List.getElem_range,List.getElem_ofFn,baseLen,Fin.ext_iff,IndexedFactorBase.genCoord]

def coord0 (b : ℕ) (w : W) := PolyT.bval (w.take b)
def readPoint (b : ℕ) (w : W) := encodeNatListBin [coord0 b w,coord0 b (w.drop b),coord0 b ((w.drop b).drop b)]
def readMany (b n : ℕ) (w : W) := (List.range n).map fun i => readPoint b (w.drop (i*(3*b)))
def prefixToTupleWords (b m : ℕ) (pre : W) :=
  (readMany b (2*m) pre,readMany b (2*m) (pre.drop (2*m*(3*b))))

@[fun_prop] theorem prefixToTupleWords_poly {b m : α → ℕ} {s : α → W} (hb : PolyT b)
    (hm : Unary (fun x => 2*m x)) (hmp : PolyT m) (hs : PolyT s) : PolyT fun x => prefixToTupleWords (b x) (m x) (s x) := by
  have hr := PolyT.range hm; have hp : PolyT fun x => 2*m x := by simpa using PolyT.length hr
  unfold prefixToTupleWords readMany readPoint coord0; fun_prop

private def pts (FB : IndexedFactorBase E.toAffine.Point m) (X : FB.BlockTuple) :=
  (List.finRange m).flatMap fun i => [(FB.blocks i).get (X i 0),(FB.blocks i).get (X i 1)]
def bits (b : ℕ) (A : E.toAffine.Point) := (pointCoords A).flatMap (w3_bits b)

private theorem little (b x : ℕ) (h : x < 2^b) : PolyT.bval (w3_bits b x) = x := by
  unfold w3_bits
  induction b generalizing x with
  | zero =>
    obtain rfl : x=0 := by simpa using h
    rfl
  | succ b ih =>
    rw [List.ofFn_succ,PolyT.bval_cons]; simp only [Fin.val_zero,Fin.val_succ,Nat.testBit_succ]
    rw [ih (x/2) ((Nat.div_lt_iff_lt_mul (by decide)).2 (by simpa [pow_succ] using h)),Nat.testBit_zero]
    by_cases h : x%2=1 <;> simp [h] <;> omega

private theorem firstPoint_ok (b : ℕ) (hb : 1 < 2^b) (hp : p ≤ 2^b) (A : E.toAffine.Point) (rest : W) :
    readPoint b (bits b A ++ rest) = encP A := by
  have r (x : ℕ) (xs : W) : (w3_bits b x ++ xs).take b = w3_bits b x ∧ (w3_bits b x ++ xs).drop b = xs := by
    have h : (w3_bits b x).length = b := List.length_ofFn
    constructor <;> conv_lhs => arg 1; rw [← h]
    · exact List.take_append_length
    · exact List.drop_append_length
  cases A <;> simp [bits,pointCoords,readPoint,coord0,List.append_assoc,(r _ _).1,(r _ _).2,little _ _ hb,little _ 0 (by positivity),little _ _ (lt_of_lt_of_le (ZMod.val_lt _) hp)]

private theorem readMany_ok (b : ℕ) (hb : 1 < 2^b) (hp : p ≤ 2^b) (xs : List E.toAffine.Point) (rest : W) :
    readMany b xs.length (xs.flatMap (bits b) ++ rest) = xs.map encP := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have hl : (bits b a).length = 3*b := by cases a <;> simp [bits,pointCoords,w3_bits] <;> omega
    simp only [readMany,List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map,List.flatMap_cons,List.append_assoc,List.map_cons,Nat.zero_mul,List.drop_zero,firstPoint_ok _ hb hp]
    congr 1; simpa only [readMany,Function.comp_def,Nat.succ_mul,← hl,Nat.add_comm _ (bits b a).length,List.drop_length_add_append] using ih

theorem prefixToTupleWords_correct (b : ℕ) (hb : 1 < 2^b) (hp : p ≤ 2^b)
    (FB : IndexedFactorBase E.toAffine.Point m) (X Y : FB.BlockTuple) :
    prefixToTupleWords b m (w3_tupleWord FB (bits b) X Y) = (words FB encP X,words FB encP Y) := by
  have H (T : FB.BlockTuple) : (pts FB T).length = 2*m := by simp [pts,List.length_flatMap]; omega
  have H' (T : FB.BlockTuple) : ((pts FB T).flatMap (bits b)).length = 2*m*(3*b) := by
    have h (a : E.toAffine.Point) : (bits b a).length = 3*b := by cases a <;> simp [bits,pointCoords,w3_bits] <;> omega
    simp [List.length_flatMap,h,H,Nat.mul_comm]
  have hw (T : FB.BlockTuple) : (pts FB T).map encP = words FB encP T := by simp [pts,W3C.BlockLookup.words,List.map_flatMap]
  have hcode : w3_tupleWord FB (bits b) X Y = (pts FB X).flatMap (bits b) ++ (pts FB Y).flatMap (bits b) := by
    simp [w3_tupleWord,pts,List.flatMap_assoc,show List.finRange 2 = [0,1] from rfl]
  rw [prefixToTupleWords,hcode,← H' X,List.drop_append_length,← H X,readMany_ok _ hb hp,hw]
  simpa [H,hw] using congrArg (fun z => (words FB encP X,z)) (readMany_ok b hb hp (pts FB Y) [])

@[fun_prop] theorem seedNatWord_poly {b m : α → ℕ} {s : α → W}
    (hb : PolyT b) (hm : Unary m) (hs : PolyT s) : PolyT fun x => seedNatWord (b x) (m x) (s x) := by
  have hr := PolyT.range hm
  unfold seedNatWord seedNatList seedChunk; fun_prop

def nativePayload (b m M : ℕ) (inp plan blk rep pre : W) : W :=
  queryPayload (curveWord inp) (encodeNatListBin (firstPointCoords inp)) (encodeNatListBin [M,threshold plan])
    (seedNatWord b m (seedBits plan)) blk (encodeNatListBin (W3C.NewtonPoly.repLabels rep)) pre

@[fun_prop] theorem nativePayload_poly {b m M : α → ℕ} {inp plan blk rep pre : α → W}
    (hb : PolyT b) (hm : Unary m) (hM : PolyT M) (hi : PolyT inp) (hp : PolyT plan)
    (hk : PolyT blk) (hr : PolyT rep) (hf : PolyT pre) :
    PolyT fun x => nativePayload (b x) (m x) (M x) (inp x) (plan x) (blk x) (rep x) (pre x) := by
  unfold nativePayload; fun_prop

export W3C.BlockLookup (initRowCounts_correct shiftRowCounts_correct)
export W3C.NewtonPoly (updateWord_correct)

end DetDLP.M3D.ECQueryOps



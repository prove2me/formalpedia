-- Prove2me | Definitions.Def_DetDLP_S6B_Words
-- name    : DetDLP_S6B_Words
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T05:01:34.60875+00:00
-- url     : https://prove2.me/theorems/487af105-2773-4062-b4d8-36f4b0286b9d
-- title:
--   Canonical query words and prefix corrections for bounded divisor search
-- statement:
--   For a nonzero integer encoded in its canonical binary word and any partial little-endian prefix, explicit polynomial-time functions print the contraction input and the number of compatible trivial factor pairs. The input agrees bit for bit with the canonical encoding of the pinned graph, and the correction counts precisely those of the two pairs that extend the prefix.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3, Proposition 2.6 (pp. 10–11)

import Definitions.Def_DetDLP_S6B_Graph
import Definitions.Def_DetDLP_S6B_Prefix
import Definitions.Def_DetDLP_S6B_Port

set_option autoImplicit false
namespace DetDLP.S6BWords
open Groundwork Groundwork.PolyT w4_MulParams w4_M5GraphBounds w4_M5GateOps w4_M5Evaluator w5_M6PinnedCount w5_M6DivisorConstraints S6BPrefix
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
attribute [local fun_prop] Groundwork.PolyT.map Groundwork.PolyT.flatMap Groundwork.PolyT.comp Groundwork.PolyT.fst Groundwork.PolyT.snd Groundwork.PolyT.const Groundwork.PolyT.length Groundwork.PolyT.mul Groundwork.PolyT.testBit Groundwork.PolyT.all Groundwork.PolyT.prodMk P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_ite__226169acf219 P2M_Groundwork_PolyT_cons__3a60f43a3b86 w5_M6Sort.cw_poly S6BGraph.image_poly J_poly n0_poly L1_poly L2_poly
abbrev Wd := List Bool
def pad (w : Wd) : Pad := w.map (fun _ => ())
def coords (w : Wd) (c : ℕ) := List.range (c*w.length)
private theorem coords_eq (w : Wd) (c : ℕ) (hc : c ≤ 1100) : coords w c = List.range (cap (pad w) (c*w.length)) := by
  have h := Nat.mul_le_mul_right w.length hc
  simp only [coords,cap,pad,List.length_map,min_eq_left (show c*w.length ≤ 1100*(w.length+1) by omega)]
@[local fun_prop] theorem coords_poly {α} [Enc α] {w : α → Wd} (hw : PolyT w) (c : ℕ) (hc : c ≤ 1100) : PolyT (fun x => coords (w x) c) := by
  simp only [coords_eq _ c hc]; apply Groundwork.PolyT.range; apply cap_unary
  · unfold pad; fun_prop
  · fun_prop
private theorem asFin (n : ℕ) : List.range n = (List.finRange n).map Fin.val := by apply List.ext_getElem <;> simp
private theorem map_coords (w : Wd) (c : ℕ) (f : ℕ → Bool) : (coords w c).map f = List.ofFn (fun i : Fin (c*w.length) => f i.val) := by rw [coords,asFin,List.map_map,List.ofFn_eq_map]; rfl

theorem bit_eq (d n : ℕ) (i : Fin d) : n.testBit i.val = natWord d n i := by
  induction d generalizing n with
  | zero => exact i.elim0
  | succ d ih => refine Fin.cases ?_ (fun j => ?_) i
                 · simp [natWord,Nat.testBit_zero,beq_iff_eq,decide_eq_true_eq]; rfl
                 · simpa [natWord,Nat.testBit_succ] using ih (n/2) j

def desc (w p : Wd) := (coords w 2).map ((bval w).testBit) ++ (coords w 4).map (fun i => (p[i]?).isSome) ++ (coords w 4).map (fun i => p[i]?.getD false)

theorem desc_eq (w p : Wd) : desc w p = pinnedDesc w.length (bval w) (pins p) := by simp only [desc,pinnedDesc,map_coords,bit_eq,pins]

@[local fun_prop] theorem desc_poly {α} [Enc α] {w p : α → Wd} (hw : PolyT w) (hp : PolyT p) : PolyT (fun x => desc (w x) (p x)) := by
  have h2 := coords_poly hw 2 (by decide)
  have h4 := coords_poly hw 4 (by decide)
  have hn := Groundwork.PolyT.ofBits hw
  unfold desc; fun_prop

def pair (s a : Wd) := s.flatMap (fun b => [true,b]) ++ [false] ++ a
@[simp] theorem pair_eq (s a : Wd) : pair s a = Encoding.frame s ++ a := by
  unfold pair; congr 1; induction s with
  | nil => rfl
  | cons b s ih => simpa only [Encoding.frame,List.flatMap_cons,List.cons_append,List.nil_append,List.append_assoc,List.singleton_append,List.foldr_cons] using congrArg (fun t => true :: b :: t) ih
@[local fun_prop] theorem pair_poly {α} [Enc α] {f g : α → Wd} (hf : PolyT f) (hg : PolyT g) : PolyT (fun x => pair (f x) (g x)) := by unfold pair; fun_prop

def inst (w p : Wd) := Encoding.encodeList id [desc w p,S6BGraph.image (pad w),countWord (scale w.length),countWord (edgeCount w.length (w4_M5GraphBounds.W w.length)+1),countWord 1]

theorem inst_eq (w p : Wd) (hd : 1 ≤ w.length) : inst w p = S6BCountCall.instanceWord hd (bval w) (pins p) := by
  have hpad : (pad w).length = w.length := by simp [pad]
  have aux (d) (q : Pad) (eq : q.length = d) (h : 1 ≤ d) : S6BGraph.image q = (graph d h).encode := by subst d; exact S6BGraph.image_graph q h
  simp only [inst,desc_eq,aux w.length (pad w) hpad hd,S6BCountCall.instanceWord,encodeBTNInstance]; rfl

private lemma frame_flat (w : Wd) : Encoding.frame w = w.flatMap (fun b => [true,b]) ++ [false] := by simpa [pair] using (pair_eq w []).symm
@[local fun_prop] theorem inst_poly {α} [Enc α] {w p : α → Wd} (hw : PolyT w) (hp : PolyT p) : PolyT (fun x => inst (w x) (p x)) := by
  have hg := S6BGraph.image_poly (q := fun x => pad (w x)) (by unfold pad; fun_prop)
  simp only [inst,Encoding.encodeList,id_eq,frame_flat,scale,edgeCount,w4_M5GraphBounds.W]; fun_prop

def factorBit (d a b n i : ℕ) := if i < d then a.testBit i else if i < 2*d then b.testBit (i-d) else n.testBit (i-2*d)
theorem factorBit_eq (d a b n : ℕ) (i : Fin (4*d)) : factorBit d a b n i.val = factorWord d a b n i := by
  simp only [factorBit,factorWord,packWords]; split <;> rename_i h
  · exact bit_eq d a ⟨_,h⟩
  · split <;> rename_i h'
    · exact bit_eq d b ⟨_,by omega⟩
    · exact bit_eq (2*d) n ⟨_,by omega⟩

def consistent (w p : Wd) (a b : ℕ) := (coords w 4).all (fun i => !(p[i]?).isSome || (factorBit w.length a b (bval w) i == (p[i]?).getD false))

theorem consistent_eq (w p : Wd) (a b : ℕ) : consistent w p a b = matchesPinsBool (pins p) (factorWord w.length a b (bval w)) := by
  simp only [consistent,coords,asFin,List.all_map,matchesPinsBool,pins]; congr 1; funext i; simp only [Function.comp_apply,factorBit_eq]; cases p[i.val]? <;> rfl

def threshold (w p : Wd) := (if consistent w p 1 (bval w) then 1 else 0) + (if consistent w p (bval w) 1 then 1 else 0)
theorem threshold_eq (w p : Wd) : threshold w p = trivialCount (factorWord w.length 1 (bval w) (bval w)) (factorWord w.length (bval w) 1 (bval w)) (pins p) := by simp only [threshold,consistent_eq,trivialCount]
@[local fun_prop] theorem consistent_poly {α} [Enc α] {w p : α → Wd} {a b : α → ℕ} (hw : PolyT w) (hp : PolyT p) (ha : PolyT a) (hb : PolyT b) : PolyT (fun x => consistent (w x) (p x) (a x) (b x)) := by
  have h4 := coords_poly hw 4 (by decide)
  unfold consistent factorBit; fun_prop
@[local fun_prop] theorem threshold_poly {α} [Enc α] {w p : α → Wd} (hw : PolyT w) (hp : PolyT p) : PolyT (fun x => threshold (w x) (p x)) := by unfold threshold; fun_prop
end DetDLP.S6BWords



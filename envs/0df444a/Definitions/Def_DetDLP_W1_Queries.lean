-- Prove2me | Definitions.Def_DetDLP_W1_Queries
-- name    : DetDLP_W1_Queries
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T01:22:51.730845+00:00
-- url     : https://prove2.me/theorems/207bccf6-7600-4253-9cf5-8ddc1b71ed06
-- title:
--   Framed query extraction for prime-field discrete logarithms
-- statement:
--   A bounded cursor reads one framed word and its remainder in polynomial time. Iterating this operation extracts the primitive-root query, the two full-group logarithm queries, and the three natural-number arguments of the residue calculation. Correctness holds for the raw binary encodings, including zero.

import Definitions.Def_DetDLP_W1_EuclidPoly

set_option autoImplicit false
namespace DetDLP_W1_Queries
open Groundwork DetDLP OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
attribute [local fun_prop] PolyT.fst PolyT.snd PolyT.comp PolyT.prodMk PolyT.const PolyT.id' P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_cons__3a60f43a3b86 P2M_Groundwork_PolyT_cond__4c673073da15 P2M_Groundwork_PolyT_ite__226169acf219 PolyT.optionElim DetDLP_W1_Euclid.poly_answer
abbrev W := List Bool
abbrev Cursor := W × W
def advance (c : Cursor) (_ : Bool) : Cursor :=
  bif c.2.headD false then (c.2.tail.headD false :: c.1,c.2.tail.tail) else c

def parse (w : W) := w.foldl advance ([],w.tail)
def first (w : W) := (parse w).1.reverse
def more (w : W) := (parse w).2.tail
private theorem parse_aux (x xs acc : W) : ∀ (fuel : W), x.length ≤ fuel.length →
    fuel.foldl advance (acc,Encoding.frame x ++ xs) = (x.reverse ++ acc,false :: xs) := by
  induction x generalizing acc with
  | nil => intro fuel _; induction fuel <;> simp_all [Encoding.frame,advance,List.foldl]
  | cons b x ih => intro fuel hf; cases fuel with
    | nil => simp at hf
    | cons k fuel => simpa [Encoding.frame,advance,List.foldl,List.append_assoc] using ih (b::acc) fuel (by simpa using hf)

private theorem flen (x : W) : (Encoding.frame x).length = 2*x.length+1 := by
  induction x with
  | nil => rfl
  | cons b x ih => change (Encoding.frame x).length + 1 + 1 = 2*(x.length+1)+1; omega

@[simp] theorem first_cons {α : Type} (f : α → W) (a : α) (as : List α) : first (Encoding.encodeList f (a::as)) = f a := by
  unfold first parse; simp only [Encoding.encodeList,List.tail_cons]
  rw [parse_aux]; simp; simp [flen]; omega
@[simp] theorem more_cons {α : Type} (f : α → W) (a : α) (as : List α) : more (Encoding.encodeList f (a::as)) = Encoding.encodeList f as := by
  unfold more parse; simp only [Encoding.encodeList,List.tail_cons]; rw [parse_aux]; rfl; simp [flen]; omega

theorem parse_poly : PolyT parse := by
  apply PolyT.foldl_add (l:=fun w : W => w) (a:=fun w => ([],w.tail)) (g:=fun _ c b => advance c b)
  · fun_prop
  · fun_prop
  · unfold advance; fun_prop
  · refine ⟨fun _ => 3,PB.const 3,?_⟩
    intro w c b _; rcases c with ⟨x,y⟩; unfold advance; dsimp only [Prod.fst,Prod.snd]; cases h : y.headD false <;> simp [len_pair,len_bools] <;> omega

@[local fun_prop] theorem first_poly {α : Type} [Enc α] {f : α → W} (hf : PolyT f) : PolyT (fun x => first (f x)) :=
  PolyT.reverse (PolyT.fst (PolyT.comp parse_poly hf))
@[local fun_prop] theorem more_poly {α : Type} [Enc α] {f : α → W} (hf : PolyT f) : PolyT (fun x => more (f x)) :=
  PolyT.tail (PolyT.snd (PolyT.comp parse_poly hf))

def second (w : W) := first (more w)
def third (w : W) := second (more w)
def frame (w : W) := w.flatMap (fun b => [true,b]) ++ [false]
@[simp] theorem frame_correct (w : W) : frame w = Encoding.frame w := by induction w <;> simp_all [frame,Encoding.frame,List.foldr]
@[local fun_prop] theorem frame_poly {α : Type} [Enc α] {f : α → W} (hf : PolyT f) : PolyT (fun x => frame (f x)) := by
  unfold frame; apply PolyT.append; apply PolyT.flatMap (f:=fun _ b => [true,b]); fun_prop; exact hf; fun_prop

def triple (a b c : W) : W := true :: (frame a ++ true :: (frame b ++ true :: (frame c ++ [false])))
def q1 := first
def q2 (w : W) := triple (first (first w)) (second w) (second (first w))
def q3 (w : W) := triple (first (first (first w))) (second (first w)) (third (first (first w)))
def q4 (w : W) := (DetDLP_W1_Euclid.answer ((PolyT.bval (first (first (first (first w))))) - 1)
  (PolyT.bval (second (first w))) (PolyT.bval (second w))).elim [false] (fun n => true :: countWord n)

theorem pq1 : PolyT q1 := first_poly (PolyT.id')
theorem pq2 : PolyT q2 := by unfold q2 triple second; fun_prop
theorem pq3 : PolyT q3 := by unfold q3 triple third second; fun_prop
theorem pq4 : PolyT q4 := by unfold q4 second countWord; fun_prop
@[simp] theorem decode_count (n : ℕ) : PolyT.bval (countWord n) = n := by
  by_cases h : n = 0; subst n; rfl; simpa [countWord,h] using PolyT.bval_bits n

abbrev saved (w r : W) := Encoding.encodeList id [w,r]
@[simp] theorem q1_spec (p g t : ℕ) : q1 (encodeFpDLPInput p g t) = countWord p := by simp [q1,encodeFpDLPInput,encodeNatListBin]
@[simp] theorem q2_spec (p g t h : ℕ) : q2 (saved (encodeFpDLPInput p g t) (countWord h)) = encodeFpDLPInput p h g := by
  simp [q2,second,saved,encodeFpDLPInput,encodeNatListBin,triple]; rfl
@[simp] theorem q3_spec (p g t h u : ℕ) : q3 (saved (saved (encodeFpDLPInput p g t) (countWord h)) (countWord u)) = encodeFpDLPInput p h t := by
  simp [q3,third,second,saved,encodeFpDLPInput,encodeNatListBin,triple]; rfl
@[simp] theorem q4_spec (p g t h u v : ℕ) : q4 (saved (saved (saved (encodeFpDLPInput p g t) (countWord h)) (countWord u)) (countWord v)) = encodeOptionNatBin (DetDLP_W1_Euclid.answer (p-1) u v) := by
  simp [q4,second,saved,encodeFpDLPInput,encodeNatListBin]; cases DetDLP_W1_Euclid.answer (p-1) u v <;> rfl
end DetDLP_W1_Queries



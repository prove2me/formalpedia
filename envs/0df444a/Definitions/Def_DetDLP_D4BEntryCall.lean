-- Prove2me | Definitions.Def_DetDLP_D4BEntryCall
-- name    : DetDLP_D4BEntryCall
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T06:33:03.905859+00:00
-- url     : https://prove2.me/theorems/d86895e7-ab48-4d80-bd7a-6d17c22bf338
-- title:
--   Two-round one-source-call controller for residual digit words
-- statement:
--   The controller queries the source machine once, then applies the digit postprocessor. Its transcript length is polynomial in the port query and the returned coefficient word, independently of source running time.

import Definitions.Def_DetDLP_D4BEntryFuel
import Theorems.Thm_DetDLP_m89_polyT_oracle_loop
set_option autoImplicit false
namespace DetDLP.D4BEntry
open Groundwork Groundwork.PolyT DetDLP_W1_Queries D4Slice
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
attribute [local fun_prop] PolyT.comp PolyT.const PolyT.fst PolyT.snd PolyT.prodMk PolyT.flatMap
  P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_cons__3a60f43a3b86 P2M_Groundwork_PolyT_ite__226169acf219
  frame_poly first_poly more_poly sourceQuery_poly pad_poly sliceArgs_poly raw_poly

def pair (x y : W) := DetDLP_W1_Queries.frame x ++ y
@[local fun_prop] theorem pair_poly {α : Type} [Enc α] {s t : α → W} (hs : PolyT s) (ht : PolyT t) : PolyT fun a => pair (s a) (t a) := by unfold pair; fun_prop
private theorem extract (w r acc : W) : ∀ fuel : W, w.length ≤ fuel.length →
    fuel.foldl advance (acc,Encoding.frame w ++ r) = (w.reverse ++ acc,false :: r) := by
  induction w generalizing acc with
  | nil => intro fuel _; induction fuel <;> simp_all [Encoding.frame,advance,List.foldl]
  | cons b w ih => intro fuel hf; cases fuel with
    | nil => simp at hf
    | cons _ fuel => simpa [Encoding.frame,advance,List.foldl,List.append_assoc] using ih (b::acc) fuel (by simpa using hf)
@[simp] theorem pair_first (s t : W) : first (true :: pair s t) = s := by
  unfold first parse pair; rw [frame_correct]; simp only [List.tail_cons]; rw [extract]; simp; simp [flen]; omega
@[simp] theorem pair_more (s t : W) : more (true :: pair s t) = t := by
  unfold more parse pair; rw [frame_correct]; simp only [List.tail_cons]; rw [extract]; rfl; simp [flen]; omega

def process (k : ℕ) (w src : W) := D4Slice.raw (sliceArgs w src (pad k w))
def controller (k : ℕ) (w : W) : W :=
  let st := first (true :: w); let ans := more (true :: w)
  if ans = [] then false :: pair st (sourceQuery st) else true :: process k st ans
@[local fun_prop] theorem process_poly {α : Type} [Enc α] (k : ℕ) {w s : α → W} (hw : PolyT w) (hs : PolyT s) : PolyT (fun a => process k (w a) (s a)) := by unfold process; fun_prop
theorem controller_poly (k : ℕ) : PolyT (controller k) := by unfold controller; fun_prop

def capLen (k : ℕ) (w src : W) := (pair w []).length + (pair w (sourceQuery w)).length + src.length + (pair w src).length + (process k w src).length

theorem call (k : ℕ) (B : PrimitiveMachine) (o : Fin B.tapeCount) :
    ∃ (D : PrimitiveMachine) (od : Fin D.tapeCount) (L : ℕ), ∀ (w src : W) (τ σ : ℝ), src ≠ [] → 0 ≤ τ → 0 ≤ σ →
      RunsWithin B o (sourceQuery w) src τ σ → RunsWithin D od w (process k w src)
        (2*(polyBound L (capLen k w src) + L*(τ+σ+1))) (polyBound L (capLen k w src)+L*(σ+1)) := by
  obtain ⟨D,od,L,_,H⟩ := m89_polyT_oracle_loop _ (controller_poly k) B o
  refine ⟨D,od,L,?_⟩; intro w src τ σ hne ht hs hb
  apply H τ σ ht hs 2 (capLen k w src) w _ (by decide)
  right; refine ⟨w,sourceQuery w,src,?_,?_,?_,?_,hb,?_⟩
  · change controller k (pair w []) = false :: pair w (sourceQuery w); simp [controller]
  · change (pair w []).length ≤ capLen k w src; unfold capLen; omega
  · change (pair w (sourceQuery w)).length ≤ capLen k w src; unfold capLen; omega
  · unfold capLen; omega
  · left; refine ⟨?_,?_,?_⟩
    · change controller k (pair w src) = true :: process k w src; simp [controller,hne]
    · change (pair w src).length ≤ capLen k w src; unfold capLen; omega
    · unfold capLen; omega

theorem capPB (k : ℕ) : ∃ j : ℕ, ∀ (w src : W), capLen k w src ≤ np j (w.length+src.length) := by
  have h : PolyT (fun p : W × W => pair p.1 [] ++ pair p.1 (sourceQuery p.1) ++ p.2 ++ pair p.1 p.2 ++ process k p.1 p.2) := by fun_prop
  obtain ⟨_,j,_,H⟩ := h
  have hz : PB (fun n => 3*n+8) := ((PB.const 3).mul PB.id').add (PB.const 8)
  have hj : PB (np j) := ⟨j,fun _ => le_rfl⟩
  obtain ⟨t,T⟩ := hj.comp hz
  refine ⟨t,fun w src => le_trans ?_ (T (w.length+src.length))⟩
  have hh := H (w,src); simp only [len_pair,len_bools,List.length_append] at hh; change _ ≤ np j _
  unfold capLen np
  apply le_trans (b := j * (3 * w.length + 2 + (3 * src.length + 2) + 2 + 1)^j) (by omega)
  apply Nat.mul_le_mul_left; apply Nat.pow_le_pow_left; omega
end DetDLP.D4BEntry



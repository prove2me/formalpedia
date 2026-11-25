-- Prove2me | Definitions.Def_DetDLP_W3C_BlockLookup
-- name    : DetDLP_W3C_BlockLookup
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T09:21:28.10866+00:00
-- url     : https://prove2.me/theorems/971b4244-f929-49c8-91d0-38371e835630
-- title:
--   PolyT factor-block list parser and incidence-row builder for Stage II
-- statement:
--   ## Overview
--   Defines a polynomial-time framed-list decoder decodeFrames with exact inverse correctness for Encoding.encodeList, plus a nested decoder for block encodings. It builds word-based incidence counters over flattened factor blocks and dedicated generator/target coordinates.
--
--   ## Complexity and correctness
--   The decoder and row builders are proved Groundwork.PolyT. Under per-block noduplication, initRowCounts_correct and shiftRowCounts_correct prove that the produced integer rows, reduced modulo M, agree coordinatewise with the Stage II initial and shift rows (w3_initRows and w3_shiftRow).
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_W3C_NewtonPoly

namespace DetDLP.W3C.BlockLookup
open Groundwork DetDLP_W1_Queries OAI.Algorithms.SubexponentialSAT
attribute [local fun_prop] PolyT.fst PolyT.snd PolyT.comp PolyT.prodMk PolyT.id' PolyT.const PolyT.mul PolyT.decide_lt PolyT.map PolyT.sum PolyT.length PolyT.idxOf PolyT.getD PolyT.flatten first_poly more_poly P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_cons__3a60f43a3b86 P2M_Groundwork_PolyT_ite__226169acf219
variable {α : Type} [Enc α]
abbrev Blocks := List (List W)
private def step (n : ℕ) (c : List W × W) (_ : Bool) : List W × W :=
  if c.2.headD false = true then ((first c.2 |>.take n) :: c.1, (more c.2).take n) else c
def decodeFrames (w : W) := (w.foldl (step w.length) ([],w)).1.reverse
@[fun_prop] theorem decodeFrames_poly {f : α → W} (hf : PolyT f) : PolyT fun x => decodeFrames (f x) := by
  apply PolyT.reverse; apply PolyT.fst; apply PolyT.foldl_add hf (by fun_prop) (by unfold step; fun_prop)
  obtain ⟨_,t,ht,_,_,hlen⟩ := hf.elim
  refine ⟨fun n => 6*t n+8, ((PB.const 6).mul ht).add (PB.const 8), ?_⟩
  intro x ⟨acc,w⟩ e he; have h := hlen x; rw [len_bools] at h; unfold step; split
  · simp only [len_pair,len_cons,len_bools,List.length_take]; omega
  · omega
private theorem frameLen (a : W) : a.length ≤ (Encoding.frame a).length := by
  induction a with | nil => simp | cons b a ih => change a.length+1 ≤ (Encoding.frame a).length+1+1; omega
private theorem run (xs : List W) (acc : List W) (fuel : W) (n : ℕ) (hn : (Encoding.encodeList id xs).length ≤ n)
    (hf : xs.length ≤ fuel.length) : (fuel.foldl (step n) (acc,Encoding.encodeList id xs)).1 = xs.reverse ++ acc := by
  induction xs generalizing acc fuel with
  | nil => induction fuel <;> simp_all [Encoding.encodeList,step,List.foldl]
  | cons a xs ih => cases fuel with
    | nil => simp at hf
    | cons b fuel =>
      have ha := frameLen a
      have h := hn; simp only [Encoding.encodeList,id_eq,List.length_cons,List.length_append] at h
      simp only [List.foldl_cons,step,show (Encoding.encodeList id (a::xs)).headD false = true from rfl,if_true,first_cons,more_cons,id_eq,List.take_of_length_le (show a.length ≤ n by omega),List.take_of_length_le (show (Encoding.encodeList id xs).length ≤ n by omega)]
      simpa using ih (a::acc) fuel (by omega) (by simpa using hf)
@[simp] theorem decodeFrames_correct (xs : List W) : decodeFrames (Encoding.encodeList id xs) = xs := by
  have h : xs.length ≤ (Encoding.encodeList id xs).length := by induction xs <;> simp_all [Encoding.encodeList]; omega
  simp [decodeFrames,run _ _ _ _ le_rfl h]

/-- The same decoder handles payloads in any canonical element encoding. -/
@[simp] theorem decodeFrames_map {β : Type*} (e : β → W) (xs : List β) :
    decodeFrames (Encoding.encodeList e xs) = xs.map e := by
  rw [← decodeFrames_correct (xs.map e)]; congr 1
  induction xs <;> simp_all [Encoding.encodeList]
def decodeBlocks (w : W) : Blocks := (decodeFrames w).map decodeFrames
@[fun_prop] theorem decodeBlocks_poly {f : α → W} (hf : PolyT f) : PolyT fun x => decodeBlocks (f x) := by unfold decodeBlocks; fun_prop
@[simp] theorem decodeBlocks_correct {β : Type*} (e : β → W) (bs : List (List β)) :
    decodeBlocks (Encoding.encodeList (Encoding.encodeList e) bs) = bs.map (List.map e) := by
  simp [decodeBlocks,List.map_map,Function.comp_def]

private def inds {β : Type} (l : List β) := List.range l.length
@[local fun_prop] private theorem indsP {β : Type} [Enc β] {l : α → List β} (hl : PolyT l) : PolyT fun x => inds (l x) := PolyT.range (Unary.of_length hl)
private def off (bs : Blocks) (i : ℕ) := ((inds bs).map fun t => if t < i then (bs.getD t []).length else 0).sum
private def hit (bs : Blocks) (xs : List W) (i s k : ℕ) := if off bs i + (bs.getD i []).idxOf (xs.getD (2*i+s) []) = k then 1 else 0
private def cnt (bs : Blocks) (xs : List W) (k : ℕ) := ((inds bs).map fun i => hit bs xs i 0 k + hit bs xs i 1 k).sum
private def coords (bs : Blocks) := inds ([] :: [] :: bs.flatten)
def initRowCounts (bs : Blocks) (u : List W) (j : ℕ) : List ℤ := (coords bs).map fun k => (if k=j then 1 else 0) - (cnt bs u k : ℤ)
def shiftRowCounts (bs : Blocks) (x y : List W) : List ℤ := (coords bs).map fun k => (cnt bs y k : ℤ) - (cnt bs x k : ℤ)
@[local fun_prop] private theorem offP {b : α → Blocks} {i : α → ℕ} (hb : PolyT b) (hi : PolyT i) : PolyT fun t => off (b t) (i t) := by unfold off; fun_prop
@[local fun_prop] private theorem hitP {b : α → Blocks} {x : α → List W} {i s k : α → ℕ} (hb : PolyT b) (hx : PolyT x) (hi : PolyT i) (hs : PolyT s) (hk : PolyT k) : PolyT fun t => hit (b t) (x t) (i t) (s t) (k t) := by unfold hit; fun_prop
@[local fun_prop] private theorem cntP {b : α → Blocks} {x : α → List W} {k : α → ℕ} (hb : PolyT b) (hx : PolyT x) (hk : PolyT k) : PolyT fun t => cnt (b t) (x t) (k t) := by unfold cnt; fun_prop
@[fun_prop] theorem initRowCounts_poly {b : α → Blocks} {u : α → List W} {j : α → ℕ} (hb : PolyT b) (hu : PolyT u) (hj : PolyT j) : PolyT fun t => initRowCounts (b t) (u t) (j t) := by unfold initRowCounts coords; fun_prop
@[fun_prop] theorem shiftRowCounts_poly {b : α → Blocks} {x y : α → List W} (hb : PolyT b) (hx : PolyT x) (hy : PolyT y) : PolyT fun t => shiftRowCounts (b t) (x t) (y t) := by unfold shiftRowCounts coords; fun_prop

variable {G : Type*} {m : ℕ} (FB : IndexedFactorBase G m) (enc : G → W)
abbrev blocks := List.ofFn fun i => (FB.blocks i).map enc
abbrev words (X : FB.BlockTuple) := (List.finRange m).flatMap fun i => [enc ((FB.blocks i).get (X i 0)), enc ((FB.blocks i).get (X i 1))]
private theorem pair_get {β : Type} (a b : β → W) (l : List β) (i : ℕ) (hi : i < l.length) (s : Fin 2) :
    (l.flatMap fun t => [a t,b t]).getD (2*i+s) [] = (if s=0 then a l[i] else b l[i]) := by
  induction l generalizing i with
  | nil => simp at hi
  | cons t ts ih => cases i with
    | zero => fin_cases s <;> rfl
    | succ i => simpa [Nat.mul_succ,show 2*i+2+s.val = (2*i+s.val+1)+1 by omega] using ih i (by simpa using hi)
private theorem word_get (X : FB.BlockTuple) (i : Fin m) (s : Fin 2) : (words FB enc X).getD (2*i.val+s) [] = enc ((FB.blocks i).get (X i s)) := by
  have eqi : (List.finRange m)[i.val] = i := by ext; simp
  rw [words,pair_get _ _ _ _ (by simp),eqi]; fin_cases s <;> rfl
private theorem rangeSum (n : ℕ) (f : ℕ → ℕ) : ((List.range n).map f).sum = ∑ i : Fin n, f i := by
  rw [Fin.sum_univ_eq_sum_range,← List.toFinset_range,List.sum_toFinset _ List.nodup_range]
private theorem block_get (i : Fin m) : (blocks FB enc).getD i [] = (FB.blocks i).map enc := by rw [List.getD_eq_getElem _ _ (by simp)]; simp
private theorem offset_eq (i : Fin m) : off (blocks FB enc) i = FB.blockOffset i := by
  simp only [off,inds,blocks,List.length_ofFn,rangeSum,IndexedFactorBase.blockOffset,Finset.sum_filter]; apply Finset.sum_congr rfl; intro t _; rw [block_get FB enc t,List.length_map]; rfl
variable (nd : ∀ i, ((FB.blocks i).map enc).Nodup)
include nd in
private theorem hit_eq (X : FB.BlockTuple) (i : Fin m) (s : Fin 2) (k : Fin FB.totalCoords) :
    hit (blocks FB enc) (words FB enc X) i s k = if FB.coordOf i (X i s) = k then 1 else 0 := by
  rw [hit,offset_eq,word_get,block_get]; have h := (nd i).idxOf_getElem (X i s).val (by simp)
  simp only [List.getElem_map] at h; rw [List.get_eq_getElem,h]; simp [IndexedFactorBase.coordOf,Fin.ext_iff]
include nd in
private theorem cnt_eq (X : FB.BlockTuple) (k : Fin FB.totalCoords) : cnt (blocks FB enc) (words FB enc X) k = FB.tupleCnt X k := by
  simp only [cnt,inds,blocks,List.length_ofFn,rangeSum,IndexedFactorBase.tupleCnt,Fin.sum_univ_two]; apply Finset.sum_congr rfl; intro i _; exact congrArg₂ (·+·) (hit_eq FB enc nd X i 0 k) (hit_eq FB enc nd X i 1 k)
private theorem coords_eq : coords (blocks FB enc) = List.range FB.totalCoords := by
  simp [coords,inds,blocks,List.length_flatten,List.ofFn_eq_map,List.map_map,Function.comp_def,IndexedFactorBase.totalCoords,IndexedFactorBase.totalBaseSize,Fin.sum_univ_def]
variable (M : ℕ)
include nd in
/-- The row for tuple `U j` occurs just after the leading generator constraint. -/
theorem initRowCounts_correct (U : Fin FB.totalCoords → FB.BlockTuple) (j : Fin FB.totalCoords) :
    ((initRowCounts (blocks FB enc) (words FB enc (U j)) j).map (fun z : ℤ => (z : ZMod M)), (0 : ZMod M)) =
    (List.ofFn ((w3_initRows FB M U)[j.val+1]'(by simp [w3_initRows])).1, ((w3_initRows FB M U)[j.val+1]'(by simp [w3_initRows])).2) := by
  simp [w3_initRows,initRowCounts,coords_eq,List.map_map]; apply List.ext_getElem <;> simp [Function.comp_def]
  intro i hi; let k : Fin FB.totalCoords := ⟨i,hi⟩; rw [cnt_eq FB enc nd (U j) k]; by_cases h : i = j.val <;> simp_all [k,w3_unitRow,Fin.ext_iff]
include nd in
/-- Coordinate reduction modulo `M` gives exactly the shift row, including its right side. -/
theorem shiftRowCounts_correct (X Y : FB.BlockTuple) :
    ((shiftRowCounts (blocks FB enc) (words FB enc X) (words FB enc Y)).map (fun z : ℤ => (z : ZMod M)), (1 : ZMod M)) =
    (List.ofFn (w3_shiftRow FB M X Y).1, (w3_shiftRow FB M X Y).2) := by
  simp [w3_shiftRow,shiftRowCounts,coords_eq,List.map_map]; apply List.ext_getElem <;> simp [Function.comp_def]
  intro i hi; let k : Fin FB.totalCoords := ⟨i,hi⟩; rw [cnt_eq FB enc nd Y k,cnt_eq FB enc nd X k]
end DetDLP.W3C.BlockLookup



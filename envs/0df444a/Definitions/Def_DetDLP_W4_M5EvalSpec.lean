-- Prove2me | Definitions.Def_DetDLP_W4_M5EvalSpec
-- name    : DetDLP_W4_M5EvalSpec
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T01:19:11.718096+00:00
-- url     : https://prove2.me/theorems/e53bd222-7b24-4b8b-b885-da4c5f0c668b
-- title:
--   Correctness of the clamped multiplication tensor evaluator
-- statement:
--   Proves that decoding legal framed port queries and evaluating with a quadratic width clamp gives precisely the requested tensor entry.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3, Lemma 2.3 (pp. 8–9)

import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Unary
import Theorems.Thm_P2M_Groundwork_PolyT_log2__935ea318e2e8
import Definitions.Def_DetDLP_W4_M5QueryBridge
import Definitions.Def_DetDLP_W4_M5PortTensor

set_option autoImplicit false

namespace DetDLP.w4_M5Evaluator
open Groundwork Groundwork.PolyT
open w4_M5QueryBridge w4_M5PortTensor w4_M5GraphBounds w4_MulParams
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

abbrev ScanState := ℕ × List Bool × List Bool

def scanStep (s : ScanState) (b : Bool) : ScanState :=
  if s.1 = 0 then
    if b then (1,s.2.1,s.2.2) else (3,s.2.1,s.2.2)
  else if s.1 = 1 then (0,b::s.2.1,s.2.2)
  else (3,s.2.1,b::s.2.2)

def splitFrame (xs : List Bool) : List Bool × List Bool :=
  let s := xs.foldl scanStep (0,[],[])
  (s.2.1.reverse,s.2.2.reverse)

def firstThree (xs : List Bool) : List Bool × List Bool × List Bool :=
  let (a,r) := splitFrame (xs.drop 1)
  let (b,s) := splitFrame (r.drop 1)
  let (c,_) := splitFrame (s.drop 1)
  (a,b,c)

def decodeNat (xs : List Bool) : ℕ := bval xs

def leafIndex (d v : ℕ) : Bool := v < 2*d || vertexCount d - 2*d ≤ v

def evalAt (d v : ℕ) (a : List Bool) : Bool :=
  if hd : 1 ≤ d then
    if hv : v < vertexCount d then
      let q : Fin (vertexCount d) := ⟨v,hv⟩
      tensor hd q (fun i => a[i.val]?.getD false)
    else false
  else false

def f (xs : List Bool) : List Bool :=
  let fs := firstThree xs
  let d := decodeNat fs.1
  let v := decodeNat fs.2.1
  let a := fs.2.2
  if leafIndex d v then [true]
  else [evalAt (min d (4096 * (xs.length+1)^2)) v a]

theorem countWord_value (n : ℕ) : decodeNat (countWord n) = n := by
  by_cases h : n = 0
  · simp [decodeNat,countWord,h,bval]
  · simp only [countWord,if_neg h,decodeNat,bval_bits]

theorem scanFrame_aux (s p : List Bool) :
    (Encoding.frame s).foldl scanStep (0,p,[]) = (3,s.reverse ++ p,[]) := by
  induction s generalizing p with
  | nil => rfl
  | cons b s ih =>
    change (Encoding.frame s).foldl scanStep (0,b::p,[]) = _
    rw [ih]; simp

private theorem scanTail_aux (s p r : List Bool) :
    s.foldl scanStep (3,p,r) = (3,p,s.reverse ++ r) := by
  induction s generalizing r with
  | nil => rfl
  | cons b s ih =>
    change s.foldl scanStep (3,p,b::r) = _
    rw [ih]; simp

theorem splitFrame_frame_append (s t : List Bool) :
    splitFrame (Encoding.frame s ++ t) = (s,t) := by
  simp [splitFrame, List.foldl_append, scanFrame_aux, scanTail_aux]

theorem splitFrame_frame (s : List Bool) : splitFrame (Encoding.frame s) = (s,[]) := by
  simpa using splitFrame_frame_append s []

theorem firstThree_query (d v : ℕ) (a : List Bool) :
    firstThree (encodePortQuery (countWord d) v a) = (countWord d,countWord v,a) := by
  simp [firstThree, encodePortQuery, Encoding.encodeList, splitFrame_frame_append]

private theorem degree_bundle {d : ℕ} (hd : 1 ≤ d) (v : Vertex d)
    (e : Fin (W d) → Edge d (W d)) (hi : Function.Injective e)
    (h : ∀ i, src hd (e i) = v ∨ dst hd (e i) = v) :
    W d ≤ (graph d hd).deg (vertexIndex d v) := by
  let G := graph d hd
  let V := vertexIndex d v
  let E := fun i => edgeIndex d (W d) (e i)
  have inc (i) : (G.endpoints (E i)).1 = V ∨ (G.endpoints (E i)).2 = V := by
    simpa only [G,E,V,graph,Equiv.symm_apply_apply,Equiv.apply_eq_iff_eq] using h i
  let f := fun i => w4_M5Network.PortLookup.index G V (E i) (inc i)
  have hf : Function.Injective f := by
    intro i j hij
    apply hi; apply (edgeIndex d (W d)).injective
    change E i = E j
    exact (w4_M5Network.PortLookup.get_index G V (E i) (inc i)).symm.trans
      ((congrArg (G.ports V).get hij).trans (w4_M5Network.PortLookup.get_index G V (E j) (inc j)))
  simpa using Fintype.card_le_of_injective f hf

private def leaf {d : ℕ} : Vertex d → Bool
  | .inputBit .. | .outputBit .. => true
  | _ => false

private theorem degree_nonleaf {d : ℕ} (hd : 1 ≤ d) (v : Vertex d) (hv : leaf v = false) :
    W d ≤ (graph d hd).deg (vertexIndex d v) := by
  let i : Fin (L1 d) := ⟨0,L1_pos d⟩
  let b : Fin (L2 d) := ⟨0,L2_pos d⟩
  cases v with
  | inputBit | outputBit => cases hv
  | pack a u => exact degree_bundle hd _ (Edge.packForward a u) (by intro x y h; injection h) (fun _ => Or.inl rfl)
  | forward1 a t => exact degree_bundle hd _ (Edge.forwardMiddle a t i) (by intro x y h; injection h) (fun _ => Or.inl rfl)
  | forward2 a j => exact degree_bundle hd _ (Edge.forwardPoint a b j) (by intro x y h; injection h) (fun _ => Or.inl rfl)
  | pointwise t j => exact degree_bundle hd _ (Edge.pointInverse t j) (by intro x y h; injection h) (fun _ => Or.inl rfl)
  | inverse1 j => exact degree_bundle hd _ (Edge.inverseMiddle b j) (by intro x y h; injection h) (fun _ => Or.inl rfl)
  | inverse2 t => exact degree_bundle hd _ (Edge.inverseMiddle t i) (by intro x y h; injection h) (fun _ => Or.inr rfl)
  | carry u => exact degree_bundle hd _ (Edge.coefficient u) (by intro x y h; injection h) (fun _ => Or.inr rfl)
  | carrySpacer u => exact degree_bundle hd _ (Edge.carryRight u) (by intro x y h; injection h) (fun _ => Or.inl rfl)

private theorem index_leaf {d : ℕ} (v : Vertex d) :
    leafIndex d (vertexIndex d v).val = leaf v := by
  cases v with
  | inputBit a u =>
    let m := (finProdFinEquiv (a,u)).val
    have hm : m < 2*d := (finProdFinEquiv (a,u)).isLt
    have eqv : (vertexIndex d (.inputBit a u)).val = m := rfl
    have h₁ : (vertexIndex d (.inputBit a u)).val < 2*d := hm
    simp [leafIndex, h₁, leaf]
  | pack a u =>
    let m := (finProdFinEquiv (a,u)).val
    have hm : m < 2*n0 d := (finProdFinEquiv (a,u)).isLt
    have eqv : (vertexIndex d (.pack a u)).val = (2*d) + (m) := rfl
    have h₁ : ¬ (vertexIndex d (.pack a u)).val < 2*d := by rw [eqv]; omega
    have h₂ : ¬ vertexCount d - 2*d ≤ (vertexIndex d (.pack a u)).val := by rw [eqv]; unfold vertexCount; omega
    simp [leafIndex, h₁, h₂, leaf]
  | forward1 a u =>
    let m := (finProdFinEquiv (a,u)).val
    have hm : m < 2*L2 d := (finProdFinEquiv (a,u)).isLt
    have eqv : (vertexIndex d (.forward1 a u)).val = (2*d) + ((2*n0 d) + (m)) := rfl
    have h₁ : ¬ (vertexIndex d (.forward1 a u)).val < 2*d := by rw [eqv]; omega
    have h₂ : ¬ vertexCount d - 2*d ≤ (vertexIndex d (.forward1 a u)).val := by rw [eqv]; unfold vertexCount; omega
    simp [leafIndex, h₁, h₂, leaf]
  | forward2 a u =>
    let m := (finProdFinEquiv (a,u)).val
    have hm : m < 2*L1 d := (finProdFinEquiv (a,u)).isLt
    have eqv : (vertexIndex d (.forward2 a u)).val = (2*d) + ((2*n0 d) + ((2*L2 d) + (m))) := rfl
    have h₁ : ¬ (vertexIndex d (.forward2 a u)).val < 2*d := by rw [eqv]; omega
    have h₂ : ¬ vertexCount d - 2*d ≤ (vertexIndex d (.forward2 a u)).val := by rw [eqv]; unfold vertexCount; omega
    simp [leafIndex, h₁, h₂, leaf]
  | pointwise a u =>
    let m := (finProdFinEquiv (a,u)).val
    have hm : m < L2 d*L1 d := (finProdFinEquiv (a,u)).isLt
    have eqv : (vertexIndex d (.pointwise a u)).val = (2*d) + ((2*n0 d) + ((2*L2 d) + ((2*L1 d) + (m)))) := rfl
    have h₁ : ¬ (vertexIndex d (.pointwise a u)).val < 2*d := by rw [eqv]; omega
    have h₂ : ¬ vertexCount d - 2*d ≤ (vertexIndex d (.pointwise a u)).val := by rw [eqv]; unfold vertexCount; omega
    simp [leafIndex, h₁, h₂, leaf]
  | inverse1 u =>
    let m := u.val
    have hm : m < L1 d := u.isLt
    have eqv : (vertexIndex d (.inverse1 u)).val = (2*d) + ((2*n0 d) + ((2*L2 d) + ((2*L1 d) + ((L2 d*L1 d) + (m))))) := rfl
    have h₁ : ¬ (vertexIndex d (.inverse1 u)).val < 2*d := by rw [eqv]; omega
    have h₂ : ¬ vertexCount d - 2*d ≤ (vertexIndex d (.inverse1 u)).val := by rw [eqv]; unfold vertexCount; omega
    simp [leafIndex, h₁, h₂, leaf]
  | inverse2 u =>
    let m := u.val
    have hm : m < L2 d := u.isLt
    have eqv : (vertexIndex d (.inverse2 u)).val = (2*d) + ((2*n0 d) + ((2*L2 d) + ((2*L1 d) + ((L2 d*L1 d) + ((L1 d) + (m)))))) := rfl
    have h₁ : ¬ (vertexIndex d (.inverse2 u)).val < 2*d := by rw [eqv]; omega
    have h₂ : ¬ vertexCount d - 2*d ≤ (vertexIndex d (.inverse2 u)).val := by rw [eqv]; unfold vertexCount; omega
    simp [leafIndex, h₁, h₂, leaf]
  | carry u =>
    let m := u.val
    have hm : m < 2*n0 d := u.isLt
    have eqv : (vertexIndex d (.carry u)).val = (2*d) + ((2*n0 d) + ((2*L2 d) + ((2*L1 d) + ((L2 d*L1 d) + ((L1 d) + ((L2 d) + (m))))))) := rfl
    have h₁ : ¬ (vertexIndex d (.carry u)).val < 2*d := by rw [eqv]; omega
    have h₂ : ¬ vertexCount d - 2*d ≤ (vertexIndex d (.carry u)).val := by rw [eqv]; unfold vertexCount; omega
    simp [leafIndex, h₁, h₂, leaf]
  | carrySpacer u =>
    let m := u.val
    have hm : m < (2*n0 d-1) := u.isLt
    have eqv : (vertexIndex d (.carrySpacer u)).val = (2*d) + ((2*n0 d) + ((2*L2 d) + ((2*L1 d) + ((L2 d*L1 d) + ((L1 d) + ((L2 d) + ((2*n0 d) + (m)))))))) := rfl
    have h₁ : ¬ (vertexIndex d (.carrySpacer u)).val < 2*d := by rw [eqv]; omega
    have h₂ : ¬ vertexCount d - 2*d ≤ (vertexIndex d (.carrySpacer u)).val := by rw [eqv]; unfold vertexCount; omega
    simp [leafIndex, h₁, h₂, leaf]
  | outputBit u =>
    let m := u.val
    have hm : m < 2*d := u.isLt
    have eqv : (vertexIndex d (.outputBit u)).val = (2*d) + ((2*n0 d) + ((2*L2 d) + ((2*L1 d) + ((L2 d*L1 d) + ((L1 d) + ((L2 d) + ((2*n0 d) + (((2*n0 d-1)) + (m))))))))) := rfl
    have h₂ : vertexCount d - 2*d ≤ (vertexIndex d (.outputBit u)).val := by rw [eqv]; unfold vertexCount; omega
    simp [leafIndex, h₂, leaf]

private theorem node_leaf_true {d : ℕ} (u : Vertex d) (h : leaf u = true) (w : Wire d) :
    node u w = true := by cases u <;> simp only [leaf] at h <;> first | contradiction | rfl

private theorem evalAt_ofFn {d : ℕ} (hd : 1 ≤ d) (v : Fin (graph d hd).nV) (a : Fin ((graph d hd).deg v) → Bool) :
    evalAt d v.val (List.ofFn a) = tensor hd v a := by
  have hv : v.val < vertexCount d := v.isLt
  unfold evalAt; rw [dif_pos hd, dif_pos hv]
  apply congrArg (tensor hd v)
  funext i
  rw [List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact i.isLt),Option.getD_some,List.getElem_ofFn]
  rfl

set_option maxHeartbeats 600000 in
theorem f_spec (d : ℕ) (hd : 1 ≤ d) (v : Fin (graph d hd).nV)
    (a : Fin ((graph d hd).deg v) → Bool) :
    f (encodePortQuery (countWord d) v.val (List.ofFn a)) = [tensor hd v a] := by
  obtain ⟨u,rfl⟩ := (vertexIndex d).surjective v
  simp only [f, firstThree_query, countWord_value, index_leaf]
  cases h : leaf u with
  | true =>
    simp only [if_true, tensor, Equiv.symm_apply_apply]
    rw [node_leaf_true u h]
  | false =>
    let N := (encodePortQuery (countWord d) (vertexIndex d u).val (List.ofFn a)).length
    have hdeg := degree_nonleaf hd u h
    have bound : J d ≤ N+1 := by
      dsimp [N]; rw [length_query,List.length_ofFn]; change J d + 1 ≤ _ at hdeg; omega
    have small : d ≤ 4096 * (N+1)^2 := by
      have h₁ := J_lower d
      have h₂ := Nat.pow_le_pow_left bound 2
      omega
    simp only [Bool.false_eq_true, if_false]
    change [evalAt (min d (4096 * (N+1)^2)) (vertexIndex d u).val (List.ofFn a)] = _
    rw [min_eq_left small]
    exact congrArg (fun b => [b]) (evalAt_ofFn hd (vertexIndex d u) a)

end DetDLP.w4_M5Evaluator



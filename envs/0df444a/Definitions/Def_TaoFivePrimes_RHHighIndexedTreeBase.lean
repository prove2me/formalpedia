-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighIndexedTreeBase
-- name    : TaoFivePrimes_RHHighIndexedTreeBase
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T01:44:12.278126+00:00
-- url     : https://prove2.me/theorems/9b17dc4c-bdb6-4e9b-8429-338439910a30
-- title:
--   TaoFivePrimes_RHHighIndexedTreeBase
-- statement:
--   Indexed finite-data tree definitions and the proved lookup/flattening identity. No approximation or RH assertion.
-- source:
--   Ordinary indexed representation of the accepted Platt/Bluestein chirp data. Original mathematical attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham; Platt DOI10.1090/mcom/3198.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighChirpData16384
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace RHHighIndexedDataTree
universe u
inductive Tree (α : Type u) where
  | leaf : List α→Tree α
  | node : Nat→Tree α→Tree α→Tree α
noncomputable def flatten {α : Type u} : Tree α→List α
  | .leaf xs => xs
  | .node _ l r => flatten l++flatten r
noncomputable def size {α : Type u} : Tree α→Nat
  | .leaf xs => xs.length
  | .node _ l r => size l+size r
noncomputable def valid {α : Type u} : Tree α→Bool
  | .leaf _ => true
  | .node n l r => decide (n=size l) && valid l && valid r
noncomputable def get {α : Type u} (d : α) : Tree α→Nat→α
  | .leaf xs,j => (xs[j]?).getD d
  | .node n l r,j => if j<n then get d l j else get d r (j-n)
lemma length_flatten {α : Type u} (t : Tree α) : (flatten t).length=size t := by
  induction t with
  | leaf xs => rfl
  | node n l r hl hr => simp only [flatten,List.length_append,size,hl,hr]
lemma get_sound {α : Type u} (d : α) (t : Tree α) (h : valid t=true) (j : Nat) :
    get d t j=((flatten t)[j]?).getD d := by
  induction t generalizing j with
  | leaf xs => rfl
  | node n l r hl hr =>
    simp only [valid,Bool.and_eq_true,decide_eq_true_eq] at h
    rcases h with ⟨⟨hn,hvl⟩,hvr⟩
    simp only [get,flatten]
    split_ifs with hj
    · rw [hl hvl]
      rw [List.getElem?_append_left (by rw [length_flatten];omega)]
    · rw [hr hvr]
      rw [List.getElem?_append_right (by rw [length_flatten];omega)]
      simp only [length_flatten,←hn]
end RHHighIndexedDataTree
noncomputable def TaoFivePrimes_RHHighIndexedTreeBase : Nat := 0



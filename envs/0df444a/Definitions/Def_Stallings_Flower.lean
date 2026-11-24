-- Prove2me | Definitions.Def_Stallings_Flower
-- name    : Stallings_Flower
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T05:13:34.880094+00:00
-- url     : https://prove2.me/theorems/748d6923-f695-4e58-b4a2-71d3fedbfedc
-- title:
--   Flower
-- statement:
--   Definitions and structural lemmas for Flower, from Arthur Freitas Ramos (Arthur742Ramos/stallings-folding; see pinned Apache-2.0 LICENSE and PROVENANCE.md)'s pinned Verified Stallings folding for finitely generated subgroups of F2 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/Flower.lean

import Definitions.Def_Stallings_Folding
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Sum.Order
import Theorems.Thm_Stallings_CosetEquivalent_trans
import Theorems.Thm_Stallings_InverseAutomaton_membershipTest_eq_true_iff
attribute [local simp] Stallings.InverseAutomaton.membershipTest_eq_true_iff


set_option autoImplicit true
namespace Stallings
def maxWordLength : List Word → Nat
  | [] => 0
  | w :: ws => max w.length (maxWordLength ws)
theorem length_le_maxWordLength_of_mem {S : List Word} {w : Word} (h : w ∈ S) :
    w.length ≤ maxWordLength S := by
  induction S with
  | nil => simp at h
  | cons u S ih =>
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact Nat.le_max_left _ _
      · exact (ih h).trans (Nat.le_max_right _ _)
abbrev FlowerVertex (S : List Word) := Option (Fin S.length × Fin (maxWordLength S + 1))
def flowerVertexOrderCode {S : List Word} :
    FlowerVertex S → Unit ⊕ₗ (Fin S.length ×ₗ Fin (maxWordLength S + 1))
  | none => toLex (Sum.inl ())
  | some p => toLex (Sum.inr (toLex p))
theorem flowerVertexOrderCode_injective {S : List Word} :
    Function.Injective (@flowerVertexOrderCode S) := by
  intro x y h
  cases x with
  | none =>
      cases y with
      | none => rfl
      | some b =>
          have hsum := toLex_inj.mp h
          cases hsum
  | some a =>
      cases y with
      | none =>
          have hsum := toLex_inj.mp h
          cases hsum
      | some b =>
          have hsum := toLex_inj.mp h
          have hp : toLex a = toLex b := Sum.inr.inj hsum
          have hab : a = b := toLex_inj.mp hp
          exact congrArg Option.some hab
instance flowerVertexLinearOrder (S : List Word) : LinearOrder (FlowerVertex S) :=
  LinearOrder.lift' flowerVertexOrderCode flowerVertexOrderCode_injective
def flowerPos (S : List Word) (i : Fin S.length) (k : Nat)
    (hk : k ≤ (S.get i).length) : FlowerVertex S :=
  if hk0 : k = 0 then none
  else if hkend : k = (S.get i).length then none
  else
    some (i, ⟨k, by
      have hkl : k < (S.get i).length := lt_of_le_of_ne hk hkend
      have hmax := length_le_maxWordLength_of_mem (List.get_mem S i)
      omega⟩)
def flowerSource (S : List Word) (i : Fin S.length) (j : Fin (S.get i).length) :
    FlowerVertex S :=
  flowerPos S i j.val (Nat.le_of_lt j.isLt)
def flowerTarget (S : List Word) (i : Fin S.length) (j : Fin (S.get i).length) :
    FlowerVertex S :=
  flowerPos S i (j.val + 1) (Nat.succ_le_of_lt j.isLt)
def flowerLabel (S : List Word) (i : Fin S.length) (j : Fin (S.get i).length) : Letter :=
  (S.get i).get j
def flowerEdge (S : List Word) (v : FlowerVertex S) (x : Letter)
    (w : FlowerVertex S) : Prop :=
  ∃ i : Fin S.length, ∃ j : Fin (S.get i).length,
    (v = flowerSource S i j ∧ w = flowerTarget S i j ∧ x = flowerLabel S i j) ∨
    (v = flowerTarget S i j ∧ w = flowerSource S i j ∧
      x = letterInv (flowerLabel S i j))
instance flowerEdgeDecidable (S : List Word) (v : FlowerVertex S) (x : Letter) :
    DecidablePred (flowerEdge S v x) := by
  intro w
  unfold flowerEdge
  infer_instance
theorem flowerEdge_inv {S : List Word} {v w : FlowerVertex S} {x : Letter}
    (h : flowerEdge S v x w) : flowerEdge S w (letterInv x) v := by
  rcases h with ⟨i, j, hforward | hbackward⟩
  · rcases hforward with ⟨hv, hw, hx⟩
    refine ⟨i, j, Or.inr ⟨hw, hv, ?_⟩⟩
    simp [hx]
  · rcases hbackward with ⟨hv, hw, hx⟩
    refine ⟨i, j, Or.inl ⟨hw, hv, ?_⟩⟩
    rw [hx]
    simp
theorem flowerEdge_inv_iff {S : List Word} (v w : FlowerVertex S) (x : Letter) :
    flowerEdge S v x w ↔ flowerEdge S w (letterInv x) v := by
  constructor
  · exact flowerEdge_inv
  · intro h
    have h' := flowerEdge_inv h
    simpa using h'
def flowerGraph (S : List Word) : InverseMultigraph (FlowerVertex S) where
  edges v x := (Finset.univ : Finset (FlowerVertex S)).filter (flowerEdge S v x)
  inverse_edges := by
    intro v x w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact flowerEdge_inv_iff v w x
def generatorSubgroup (S : List Word) : Subgroup Free :=
  Subgroup.closure (Set.range fun i : Fin S.length => wordEval (S.get i))
def flowerPotential (S : List Word) : FlowerVertex S → Free
  | none => 1
  | some (i, k) =>
      if k.val < (S.get i).length then wordEval ((S.get i).take k.val) else 1
def foldWords (S : List Word) : InverseAutomaton (FlowerVertex S) :=
  foldAutomaton (flowerGraph S) none
def foldedMembershipTest (S : List Word) (g : Free) : Bool :=
  (foldWords S).membershipTest g
end Stallings



-- Prove2me | Definitions.Def_Stallings_InverseAutomaton
-- name    : Stallings_InverseAutomaton
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T05:05:59.203699+00:00
-- url     : https://prove2.me/theorems/f98aabba-dc0a-4e47-99a8-62285cd4a909
-- title:
--   Inverse Automaton
-- statement:
--   Definitions and structural lemmas for Inverse Automaton, from Arthur Freitas Ramos (Arthur742Ramos/stallings-folding; see pinned Apache-2.0 LICENSE and PROVENANCE.md)'s pinned Verified Stallings folding for finitely generated subgroups of F2 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/InverseAutomaton.lean

import Mathlib.GroupTheory.FreeGroup.Reduce
set_option autoImplicit true
namespace Stallings
abbrev Letter := Fin 2 × Bool
abbrev Word := List Letter
abbrev Free := FreeGroup (Fin 2)
def letterInv (x : Letter) : Letter := (x.1, !x.2)
@[simp]
theorem letterInv_letterInv (x : Letter) : letterInv (letterInv x) = x := by
  cases x with
  | mk i b => cases b <;> rfl
def wordInv (w : Word) : Word := FreeGroup.invRev w
def wordEval (w : Word) : Free := FreeGroup.mk w
def letterEval (x : Letter) : Free :=
  if x.2 then FreeGroup.of x.1 else (FreeGroup.of x.1)⁻¹
@[simp]
theorem wordEval_nil : wordEval [] = 1 := by
  simpa [wordEval] using (FreeGroup.one_eq_mk : (1 : Free) = FreeGroup.mk []) |>.symm
@[simp]
theorem wordEval_append (u v : Word) : wordEval (u ++ v) = wordEval u * wordEval v := by
  simp [wordEval, FreeGroup.mul_mk]
@[simp]
theorem wordEval_singleton (x : Letter) : wordEval [x] = letterEval x := by
  cases x with
  | mk i b => cases b <;> simp [wordEval, letterEval, FreeGroup.of, FreeGroup.invRev]
@[simp]
theorem wordEval_cons (x : Letter) (w : Word) :
    wordEval (x :: w) = letterEval x * wordEval w := by
  rw [show x :: w = [x] ++ w by rfl, wordEval_append, wordEval_singleton]
@[simp]
theorem letterEval_inv (x : Letter) : letterEval (letterInv x) = (letterEval x)⁻¹ := by
  cases x with
  | mk i b => cases b <;> simp [letterInv, letterEval]
@[simp]
theorem wordEval_wordInv (w : Word) : wordEval (wordInv w) = (wordEval w)⁻¹ := by
  simp [wordEval, wordInv, FreeGroup.inv_mk]
structure InverseAutomaton (V : Type*) where
  base : V
  next : V → Letter → Option V
  inverse_next : ∀ {v x w}, next v x = some w → next w (letterInv x) = some v
namespace InverseAutomaton
variable {V : Type*} (G : InverseAutomaton V)
def run (G : InverseAutomaton V) (v : V) : Word → Option V
  | [] => some v
  | x :: w => (G.next v x).bind fun u => G.run u w
@[simp]
theorem run_nil (v : V) : G.run v [] = some v := rfl
inductive Walk : V → Word → V → Prop where
  | nil (v : V) : Walk v [] v
  | cons {v u z : V} {x : Letter} {w : Word}
      (edge : G.next v x = some u) (tail : Walk u w z) : Walk v (x :: w) z
theorem Walk.append {v u t : V} {w₁ w₂ : Word}
    (h₁ : G.Walk v w₁ u) (h₂ : G.Walk u w₂ t) : G.Walk v (w₁ ++ w₂) t := by
  induction h₁ with
  | nil => simpa using h₂
  | @cons v u z x w edge tail ih =>
      simpa using Walk.cons edge (ih h₂)
theorem Walk.invRev {v u : V} {w : Word} (h : G.Walk v w u) :
    G.Walk u (wordInv w) v := by
  induction h with
  | nil v => exact Walk.nil v
  | @cons v u z x w edge tail ih =>
      have inverseEdge : G.Walk u [letterInv x] v :=
        Walk.cons (G.inverse_next edge) (Walk.nil v)
      rw [wordInv, FreeGroup.invRev_cons]
      change G.Walk z (wordInv w ++ [letterInv x]) v
      exact Walk.append G ih inverseEdge
def loopSubgroup : Subgroup Free where
  carrier := {g | ∃ w : Word, wordEval w = g ∧ G.Walk G.base w G.base}
  one_mem' := by
    exact ⟨[], by simpa [wordEval] using FreeGroup.one_eq_mk.symm, Walk.nil G.base⟩
  mul_mem' := by
    intro g h hg hh
    rcases hg with ⟨w, hw, hwalk⟩
    rcases hh with ⟨v, hv, hvwalk⟩
    refine ⟨w ++ v, ?_, Walk.append G hwalk hvwalk⟩
    rw [wordEval_append, hw, hv]
  inv_mem' := by
    intro g hg
    rcases hg with ⟨w, hw, hwalk⟩
    refine ⟨wordInv w, ?_, Walk.invRev G hwalk⟩
    rw [wordEval_wordInv, hw]
def accepts (g : Free) : Prop := G.run G.base (FreeGroup.toWord g) = some G.base
def membershipTest [DecidableEq V] (G : InverseAutomaton V) (g : Free) : Bool :=
  if G.run G.base (FreeGroup.toWord g) = some G.base then true else false
end InverseAutomaton
end Stallings



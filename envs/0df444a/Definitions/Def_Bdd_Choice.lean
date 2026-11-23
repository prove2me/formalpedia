-- Prove2me | Definitions.Def_Bdd_Choice
-- name    : Bdd_Choice
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:08:18.668806+00:00
-- url     : https://prove2.me/theorems/fa143876-a2be-48ed-b11e-2eed2318a2d3
-- title:
--   Choice
-- statement:
--   Definitions and structural lemmas for Choice, from Eshel Yaron and contributors's pinned Correctness of binary decision diagrams for CNF formulas development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Choice.lean

import Definitions.Def_Bdd_Basic
import Theorems.Thm_Nary_restrict_const
import Theorems.Thm_OBdd_high_reduced
import Theorems.Thm_OBdd_independentOf_lt_root
import Theorems.Thm_OBdd_low_reduced
import Theorems.Thm_OBdd_var_lt_high_var
import Theorems.Thm_OBdd_var_lt_low_var
import Theorems.Thm_P2M_OBdd_evaluate_node___75814e9183f4
import Theorems.Thm_P2M_OBdd_evaluate_terminal__321343d95937
attribute [local simp] Nary.restrict_const


set_option autoImplicit true
attribute [local implicit_reducible] OBdd Bdd.Ordered
namespace Choice
open Pointer
open OBdd
def choice_helper (O : OBdd n m) : O.1.root = .node j → Vector Bool n → Vector Bool n := fun hj I ↦
  match hl : O.1.heap[j].low with
  | .node j => choice_helper (O.low hj) hl I
  | .terminal true => I.set O.1.heap[j].var false
  | .terminal false =>
    match hh : O.1.heap[j].high with
    | .terminal _ => I.set O.1.heap[j].var true
    | .node j' => (choice_helper (O.high hj) hh I).set O.1.heap[j].var true
termination_by O
decreasing_by all_goals first | exact oedge_of_low | exact oedge_of_high | decreasing_tactic
def choice (O : OBdd n m) : (∃ I, O.evaluate I) → Vector Bool n := fun ht ↦
  match O_root_def : O.1.root with
  | .terminal true => Vector.replicate n false
  | .terminal false => by
    absurd ht
    rw [OBdd.evaluate_terminal' O_root_def]
    simp only [Function.const_apply, Bool.false_eq_true, exists_const, not_false_eq_true]
  | .node j => choice_helper O O_root_def (Vector.replicate n false)
lemma Vector.get_set_ne {xs : Vector α n} {x : α} (hi : i < n) {j : Fin n} (h : i ≠ j) :
    (xs.set i x hi).get j = xs.get j := by
  exact Vector.getElem_set_ne hi j.isLt h
def choice_helper_spec' {O : OBdd n m} (hr : O.Reduced) (hj : O.1.root = .node j) (i : Fin n) :
    i < O.1.heap[j].var → (choice_helper O hj (Vector.replicate n false)).get i = false := by
  intro hi
  unfold choice_helper
  split
  next jl hl =>
    have := var_lt_low_var (h := hj)
    simp only [var, Nat.succ_eq_add_one, Bdd.var, hj, low, Bdd.low, hl, toVar] at this
    apply choice_helper_spec' (low_reduced hr)
    simp_all
    omega
  next hl => simp [Vector.get]
  next hl =>
    split
    next bh hh =>
      rw [Vector.get_set_ne]
      · simp [Vector.get]
      · omega
    next jh hh =>
      have := var_lt_high_var (h := hj)
      simp only [var, Nat.succ_eq_add_one, Bdd.var, hj, high, Bdd.high, hh, toVar] at this
      rw [Vector.get_set_ne]
      apply choice_helper_spec' (high_reduced hr)
      · simp_all
        omega
      · omega
termination_by O
decreasing_by all_goals first | exact oedge_of_low | exact oedge_of_high | decreasing_tactic
def choice_helper_spec'' {O : OBdd n m} (hr : O.Reduced) (hj : O.1.root = node j) (i : Fin n) :
    i < O.1.heap[j].var → (choice_helper O hj (Vector.replicate n false))[i] = false := by
  have := choice_helper_spec' hr hj i
  exact this
def choice_helper_spec {O : OBdd n m} (hr : O.Reduced) (hj : O.1.root = node j) :
    O.evaluate (choice_helper O hj (Vector.replicate n false)) := by
  unfold choice_helper
  split
  next jl hl =>
    rw [evaluate_node'' hj]
    simp only
    suffices s : (choice_helper (O.low hj) hl (Vector.replicate n false))[O.1.heap[j].var] = false by
      rw [s]
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply choice_helper_spec (low_reduced hr)
    rw [choice_helper_spec'' (low_reduced hr) hl]
    have := var_lt_low_var (h := hj)
    simp only [var, Nat.succ_eq_add_one, Bdd.var, toVar, hj, hl, low, Bdd.low] at this
    simp_all
  next hl =>
    rw [evaluate_node'' hj]
    have : (O.low hj).1.root = terminal true := by simp only [low, Bdd.low, hl]
    simp [evaluate_terminal' this]
  next hl =>
    split
    next bh hh =>
      rw [evaluate_node'' hj]
      have : (O.high hj).1.root = terminal true := by
        simp only [high, Bdd.high]
        rw [hh]
        congr
        cases bh with
        | false => exact False.elim (hr.1 ⟨node j, by simp_all; left⟩ ⟨by simp_all⟩)
        | true => rfl
      simp [evaluate_terminal' this]
    next jh hh =>
      rw [evaluate_node'' hj]
      simp only [Fin.getElem_fin, Vector.getElem_set_self, ↓reduceIte]
      have : (O.high hj).evaluate ((choice_helper (O.high hj) hh (Vector.replicate n false)).set O.1.heap[j.1].var.1 true) =
             (O.high hj).evaluate (choice_helper (O.high hj) hh ((Vector.replicate n false))) := by
        rw [OBdd.independentOf_lt_root (O.high hj) ⟨O.1.heap[j.1].var.1, ?_⟩ true (choice_helper (O.high hj) hh (Vector.replicate n false))]
        rw [show O.1.heap[j.1].var.1 = O.var by simp [hj]]
        exact var_lt_high_var
      rw [this]
      apply choice_helper_spec (high_reduced hr)
termination_by O
decreasing_by all_goals first | exact oedge_of_low | exact oedge_of_high | decreasing_tactic
@[simp]
def choice_evaluate {O : OBdd n m} (hr : O.Reduced) (ht : ∃ I, O.evaluate I) : O.evaluate (choice O ht) = true := by
  simp only [choice]
  split
  next O_root_def => rw [evaluate_terminal' O_root_def]; simp
  next O_root_def =>
    absurd ht
    rw [evaluate_terminal' O_root_def]
    simp only [Function.const_apply, Bool.false_eq_true, exists_const, not_false_eq_true]
  next j O_root_def => exact choice_helper_spec hr O_root_def
end Choice



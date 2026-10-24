-- Prove2me | Definitions.Def_ThreeSum19202796Base_15
-- name    : ThreeSum19202796Base_15
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-23T23:37:28.208739+00:00
-- url     : https://prove2.me/theorems/64ee3fa9-2141-43eb-b1e9-bb9322470a5b
-- title:
--   3SUM base layer — Def_ThreeSum19202796Base_15
-- statement:
--   Base-layer declarations for the ternary 3SUM transplant.
-- source:
--   https://github.com/JoshuaQFEX/3sum-bound (commit eda5da36565f) [Apache-2.0]

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
-- Recovery bundle: the Light program-logic layer (Lang.Logic) with Light tactics expanded
-- at call sites (the platform bans `macro` registration in submissions).

import Definitions.Def_ThreeSum19202796Base_13
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Proof rules for the light language

Ends lim P d s σ T Q says: the statement s, started in σ, ends within T steps in a state that
satisfies Q.  There is one rule for each construct; a rule turns a goal about a statement into goals
about its parts, so a proof follows the text of the program from top to bottom.  Recursion needs no
rule: a statement about a recursive procedure is proved by induction (in Lean) on a measure, and the
rule for calls unfolds the body.

There are three rules for loops: with an invariant indexed by the number of the round and a cost for
each round (Ends.while), the same with one cost for all rounds (Ends.whileConst), and, for a loop
whose number of rounds depends on the data, with a quantity that every round decreases
(Ends.whileVariant).

The file also has the basic facts about runs (a run stays a run when procedures are appended to the
program), notation for writing programs, the simplification set
`(simp only [Light.Expr.Safe, Light.Expr.val, Light.Expr.cost, Light.Op.eval,
            Light.Cond.Holds, Light.Cond.cost, Light.Cond.Safe,
            Function.update_apply, reduceIte, true_and, and_true, Nat.reduceEqDiff,
            Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, ])`, and the standing assumptions `Std` about the limits.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Runs -/

/-- A procedure of a program is a procedure, with the same number, of the program with more
procedures appended. -/
theorem getElem?_append_of_eq_some {P : Program} {p : ℕ} {body : Stmt} (h : P[p]? = some body)
    (R : Program) : (P ++ R)[p]? = some body := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
  exact h

/-- Procedure number i of a list that is appended to the program P₀ has the number |P₀| + i,
whatever is appended after the list. -/
theorem getElem?_append_append {P₀ B : Program} (R : Program) {i : ℕ} {body : Stmt}
    (h : B[i]? = some body) : (P₀ ++ (B ++ R))[P₀.length + i]? = some body := by
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  exact getElem?_append_of_eq_some h R

/-- Procedure number i of a list that is appended to the program P₀ has the number |P₀| + i. -/
theorem getElem?_append_length_add (P₀ : Program) {R : Program} {i : ℕ} {body : Stmt}
    (h : R[i]? = some body) : (P₀ ++ R)[P₀.length + i]? = some body := by
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  exact h


/-- A run stays a run when procedures are appended to the program. -/
theorem Exec.append {s : Stmt} {σ σ' : State} {c : ℕ} (h : Exec lim P d s σ σ' c) (R : Program) :
    Exec lim (P ++ R) d s σ σ' c := by
  induction h with
  | skip => exact .skip
  | set h => exact .set h
  | store h₁ h₂ h₃ => exact .store h₁ h₂ h₃
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | iteTrue h₁ h₂ _ ih => exact .iteTrue h₁ h₂ ih
  | iteFalse h₁ h₂ _ ih => exact .iteFalse h₁ h₂ ih
  | whileFalse h₁ h₂ => exact .whileFalse h₁ h₂
  | whileTrue h₁ h₂ _ _ ih₁ ih₂ => exact .whileTrue h₁ h₂ ih₁ ih₂
  | call h₁ h₂ h₃ _ ih => exact .call h₁ (getElem?_append_of_eq_some h₂ R) h₃ ih

/-- The statement s, started in σ, ends within T steps in a state that satisfies Q. -/
def Ends (lim : Limits) (P : Program) (d : ℕ) (s : Stmt) (σ : State) (T : ℕ) (Q : State → Prop) :
    Prop :=
  ∃ σ' c, Exec lim P d s σ σ' c ∧ c ≤ T ∧ Q σ'

/-- More time and a weaker conclusion. -/
theorem Ends.mono {s σ T T' Q Q'} (h : Ends lim P d s σ T Q) (hT : T ≤ T')
    (hQ : ∀ σ', Q σ' → Q' σ') : Ends lim P d s σ T' Q' := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he, hc.trans hT, hQ _ hq⟩

/-- What is proved about a program holds for the program with more procedures appended. -/
theorem Ends.append {s σ T Q} (h : Ends lim P d s σ T Q) (R : Program) :
    Ends lim (P ++ R) d s σ T Q := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he.append R, hc, hq⟩

theorem Ends.skip {σ T} {Q : State → Prop} (h : Q σ) : Ends lim P d .skip σ T Q :=
  ⟨σ, 0, .skip, Nat.zero_le _, h⟩

theorem Ends.set {σ T x e} {Q : State → Prop} (hs : e.Safe lim σ) (hT : e.cost + 1 ≤ T)
    (h : Q { σ with loc := Function.update σ.loc x (e.val σ) }) : Ends lim P d (.set x e) σ T Q :=
  ⟨_, _, .set hs, hT, h⟩

theorem Ends.store {σ T a e} {Q : State → Prop} (ha : a.Safe lim σ) (he : e.Safe lim σ)
    (hA : lim.Addr (a.val σ)) (hT : a.cost + e.cost + 1 ≤ T)
    (h : Q { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) }) :
    Ends lim P d (.store a e) σ T Q :=
  ⟨_, _, .store ha he hA, hT, h⟩

theorem Ends.seq {σ T s₁ s₂} {Q : State → Prop} (T₁ T₂ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' T₂ Q) (hT : T₁ + T₂ ≤ T) :
    Ends lim P d (.seq s₁ s₂) σ T Q := by
  obtain ⟨σ', c₁, he₁, hc₁, σ'', c₂, he₂, hc₂, hq⟩ := h
  exact ⟨σ'', _, .seq he₁ he₂, by omega, hq⟩

theorem Ends.ite {σ T c s₁ s₂} {Q : State → Prop} (T' : ℕ) (hs : c.Safe lim σ)
    (h₁ : c.Holds σ → Ends lim P d s₁ σ T' Q) (h₂ : ¬ c.Holds σ → Ends lim P d s₂ σ T' Q)
    (hT : c.cost + 1 + T' ≤ T) : Ends lim P d (.ite c s₁ s₂) σ T Q := by
  by_cases hv : c.Holds σ
  · obtain ⟨σ', k, he, hk, hq⟩ := h₁ hv
    exact ⟨σ', _, .iteTrue hs hv he, by omega, hq⟩
  · obtain ⟨σ', k, he, hk, hq⟩ := h₂ hv
    exact ⟨σ', _, .iteFalse hs hv he, by omega, hq⟩

/-- A loop whose test holds: one round, then the loop again. -/
theorem Ends.whileStep {σ c s T} {Q : State → Prop} (T₁ T₂ : ℕ) (hs : c.Safe lim σ) (hc : c.Holds σ)
    (h : Ends lim P d s σ T₁ fun σ' => Ends lim P d (.while c s) σ' T₂ Q)
    (hT : c.cost + 1 + T₁ + T₂ ≤ T) : Ends lim P d (.while c s) σ T Q := by
  obtain ⟨σ', c₁, he₁, hc₁, σ'', c₂, he₂, hc₂, hq⟩ := h
  exact ⟨σ'', _, .whileTrue hs hc he₁ he₂, by omega, hq⟩

/-- A loop whose test fails. -/
theorem Ends.whileDone {σ c s T} {Q : State → Prop} (hs : c.Safe lim σ) (hc : ¬ c.Holds σ)
    (hQ : Q σ) (hT : c.cost + 1 ≤ T) : Ends lim P d (.while c s) σ T Q :=
  ⟨σ, _, .whileFalse hs hc, hT, hQ⟩

/-- Loops.  I i is the invariant before round number i (counted from 0) of n rounds, and b i bounds
the cost of that round. -/
theorem Ends.while {σ c s} {Q : State → Prop} (I : ℕ → State → Prop) (n : ℕ) (b : ℕ → ℕ)
    (hI : I 0 σ)
    (hs : ∀ i σ, i < n → I i σ → c.Safe lim σ ∧ c.Holds σ ∧ Ends lim P d s σ (b i) (I (i + 1)))
    (hn : ∀ σ, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ) :
    Ends lim P d (.while c s) σ (∑ i ∈ Finset.range n, (c.cost + 1 + b i) + (c.cost + 1)) Q := by
  have aux : ∀ j i σ, i + j = n → I i σ →
      Ends lim P d (.while c s) σ
        (∑ k ∈ Finset.range j, (c.cost + 1 + b (i + k)) + (c.cost + 1)) Q := by
    intro j
    induction j with
    | zero =>
      intro i σ hij hi
      obtain rfl : i = n := by omega
      obtain ⟨h1, h2, h3⟩ := hn σ hi
      exact ⟨σ, _, .whileFalse h1 h2, by simp, h3⟩
    | succ j ih =>
      intro i σ hij hi
      obtain ⟨h1, h2, σ', k₁, he₁, hk₁, hi'⟩ := hs i σ (by omega) hi
      obtain ⟨σ'', k₂, he₂, hk₂, hq⟩ := ih (i + 1) σ' (by omega) hi'
      refine ⟨σ'', _, .whileTrue h1 h2 he₁ he₂, ?_, hq⟩
      rw [Finset.sum_range_succ']
      have : ∀ k, i + 1 + k = i + (k + 1) := fun k => by omega
      simp only [this] at hk₂
      simp only [Nat.add_zero]
      omega
  simpa using aux n 0 σ (by omega) hI

/-- Loops in which every round costs at most b. -/
theorem Ends.whileConst {σ c s T} {Q : State → Prop} (I : ℕ → State → Prop) (n b : ℕ) (hI : I 0 σ)
    (hs : ∀ i σ, i < n → I i σ → c.Safe lim σ ∧ c.Holds σ ∧ Ends lim P d s σ b (I (i + 1)))
    (hn : ∀ σ, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ)
    (hT : n * (c.cost + 1 + b) + (c.cost + 1) ≤ T) : Ends lim P d (.while c s) σ T Q :=
  (Ends.while I n (fun _ => b) hI hs hn).mono (by simpa using hT) fun _ h => h

/-- Loops whose number of rounds depends on the data.  I is the invariant, m a quantity that every
round decreases, and b bounds the cost of a round. -/
theorem Ends.whileVariant {σ c s T} {Q : State → Prop} (I : State → Prop) (m : State → ℕ) (b : ℕ)
    (hI : I σ) (hsafe : ∀ σ, I σ → c.Safe lim σ)
    (hs : ∀ σ, I σ → c.Holds σ → Ends lim P d s σ b fun σ' => I σ' ∧ m σ' < m σ)
    (hn : ∀ σ, I σ → ¬ c.Holds σ → Q σ) (hT : m σ * (c.cost + 1 + b) + (c.cost + 1) ≤ T) :
    Ends lim P d (.while c s) σ T Q := by
  have key : ∀ n σ, I σ → m σ ≤ n →
      Ends lim P d (.while c s) σ (m σ * (c.cost + 1 + b) + (c.cost + 1)) Q := by
    intro n
    induction n with
    | zero =>
      intro σ h hm
      by_cases hc : c.Holds σ
      · obtain ⟨σ₁, k₁, -, -, -, hlt⟩ := hs σ h hc
        omega
      · exact ⟨σ, _, .whileFalse (hsafe _ h) hc, by omega, hn σ h hc⟩
    | succ n ih =>
      intro σ h hm
      by_cases hc : c.Holds σ
      · obtain ⟨σ₁, k₁, he₁, hk₁, hI₁, hlt⟩ := hs σ h hc
        obtain ⟨σ₂, k₂, he₂, hk₂, hq⟩ := ih σ₁ hI₁ (by omega)
        refine ⟨σ₂, _, .whileTrue (hsafe _ h) hc he₁ he₂, ?_, hq⟩
        have h1 : (m σ₁ + 1) * (c.cost + 1 + b) ≤ m σ * (c.cost + 1 + b) :=
          Nat.mul_le_mul_right _ hlt
        have h2 : (m σ₁ + 1) * (c.cost + 1 + b) = m σ₁ * (c.cost + 1 + b) + (c.cost + 1 + b) := by
          ring
        omega
      · exact ⟨σ, _, .whileFalse (hsafe _ h) hc, by omega, hn σ h hc⟩
  exact (key _ σ hI le_rfl).mono hT fun _ h => h


/-- Local variable number x. -/
abbrev v (x : ℕ) : Expr := .var x
/-- The constant n. -/
abbrev k (n : ℕ) : Expr := .const n
infixl:65 " +' " => Expr.op Op.add
infixl:70 " *' " => Expr.op Op.mul
@[inherit_doc] infix:50 " <' " => Cond.lt
@[inherit_doc] infix:50 " =' " => Cond.eq
@[inherit_doc] infixr:30 " ;; " => Stmt.seq

/-- The test a ≤ b, written as a < b + 1. -/
abbrev Cond.le (a b : Expr) : Cond := a <' b +' k 1
@[inherit_doc] infix:50 " ≤' " => Cond.le

/-- Branching on a ≠ b: the branches of the test a = b, swapped. -/
abbrev Stmt.iteNe (a b : Expr) (s₁ s₂ : Stmt) : Stmt := .ite (a =' b) s₂ s₁

/-- The test a ≤ b holds if and only if a ≤ b. -/
theorem Cond.holds_le {σ : State} {a b : Expr} : (a ≤' b).Holds σ ↔ a.val σ ≤ b.val σ :=
  Int.lt_add_one_iff

/-! ## Simplification -/

attribute [simp] Expr.val Expr.cost Expr.Safe Op.eval Cond.Holds Cond.cost Cond.Safe frame


/-- The standing assumptions about the limits: an address fits in a word, and so do the constants
of the programs. -/
structure Std (lim : Limits) : Prop where
  space_le : (lim.space : ℤ) ≤ lim.word
  const_le : (100 : ℤ) ≤ lim.word

/-- An address fits in a word if the memory is not larger than the largest word. -/
theorem Limits.Addr.abs_le {a : ℤ} (h : lim.Addr a) (hw : (lim.space : ℤ) ≤ lim.word) :
    |a| ≤ lim.word := by
  rw [abs_of_nonneg h.1]; exact h.2.le.trans hw

/-- A natural number below the size of the memory is an address, and fits in a word. -/
theorem Limits.addr_of_lt (hw : (lim.space : ℤ) ≤ lim.word) {x : ℕ} (hx : x < lim.space) :
    lim.Addr (x : ℤ) ∧ |(x : ℤ)| ≤ lim.word := by
  have h : lim.Addr (x : ℤ) := ⟨Int.natCast_nonneg x, by exact_mod_cast hx⟩
  exact ⟨h, h.abs_le hw⟩



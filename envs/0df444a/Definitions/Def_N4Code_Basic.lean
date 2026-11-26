-- Prove2me | Definitions.Def_N4Code_Basic
-- name    : N4Code_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:55:58.653481+00:00
-- url     : https://prove2.me/theorems/4e419586-1280-5218-a114-3e19a0c19200
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Shenghao Yang, Yanyan Dong (shhyang/n4code_lean; see pinned Apache-2.0 LICENSE)'s pinned N4Code: optimal finite-length block codes of size four for binary symmetric channels development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean

import Definitions.Def_N4Code_Definitions
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
namespace N4Code
lemma colVal_le_15 (c : Column) : colVal c ≤ 15 := by
  unfold colVal
  have hstep : (∑ j : Fin 4, if c j then 2 ^ (3 - j.val) else 0) ≤
      ∑ j : Fin 4, 2 ^ (3 - j.val) := by
    apply Finset.sum_le_sum
    intro j _
    by_cases h : c j = true <;> simp [h]
  have hval : (∑ j : Fin 4, 2 ^ (3 - j.val)) = 15 := by decide
  rw [← hval]
  exact hstep
def onesOn {n : ℕ} (s : Finset (Fin n)) (y : Word n) : Finset (Fin n) :=
  s.filter fun t => y t = true
def fiber {n : ℕ} (C : Code n) (i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun t : Fin n => colVal (C t) = i
def GoodWords {n : ℕ} (C : Code n) (k : ℕ → ℕ) : Finset (Word n) :=
  (Finset.univ : Finset (Word n)).filter
    fun y : Word n => (∑ i ∈ Finset.Icc 0 15, if w_i C i y = k i then 0 else 1) = 0
def wordTuple {n : ℕ} (C : Code n) (y : Word n) : Fin 16 → Finset (Fin n) :=
  fun a => onesOn (fiber C a.val) y
def GoodTuplePred {n : ℕ} (C : Code n) (k : ℕ → ℕ) (g : Fin 16 → Finset (Fin n)) : Prop :=
  ∀ a : Fin 16, g a ∈ (fiber C a.val).powersetCard (k a.val)
instance goodTuplePredDecidable {n : ℕ} (C : Code n) (k : ℕ → ℕ) (g : Fin 16 → Finset (Fin n)) :
    Decidable (GoodTuplePred C k g) := by
  unfold GoodTuplePred
  infer_instance
def GoodTuples {n : ℕ} (C : Code n) (k : ℕ → ℕ) : Finset (Fin 16 → Finset (Fin n)) :=
  (Finset.univ : Finset (Fin 16 → Finset (Fin n))).filter fun g => GoodTuplePred C k g
def tupleWord {n : ℕ} (C : Code n) (g : Fin 16 → Finset (Fin n)) : Word n :=
  fun t => if t ∈ g ⟨colVal (C t), Nat.lt_succ_of_le (colVal_le_15 (C t))⟩ then true else false
example : alpha example74 0 = 4 := by decide
example : alpha example74 1 = 28 := by decide
example : alpha example74 2 = 52 := by decide
example : alpha example74 3 = 36 := by decide
example : alpha example74 4 = 8 := by decide
example : alpha example74 5 = 0 := by decide
example : alpha example74 6 = 0 := by decide
example : alpha example74 7 = 0 := by decide
example : (∑ d ∈ Finset.Icc 0 7, alpha example74 d) = 128 := by decide
example : hammingWeight (row example74 ⟨0, by decide⟩) = 0 := by decide
example : hammingDist (row example74 ⟨0, by decide⟩) (row example74 ⟨1, by decide⟩) = 4 := by
  decide
example : hammingDist (row example74 ⟨2, by decide⟩) (row example74 ⟨3, by decide⟩) = 4 := by
  decide
example : hammingDist (row example74 ⟨0, by decide⟩) (row example74 ⟨3, by decide⟩) = 4 := by
  decide
end N4Code



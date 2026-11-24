-- Prove2me | Definitions.Def_BalanceSpecificaton_Shortlex
-- name    : BalanceSpecificaton_Shortlex
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:35:20.599947+00:00
-- url     : https://prove2.me/theorems/02342293-c4e4-4ad8-a95a-c1fea11835fa
-- title:
--   Shortlex
-- statement:
--   Definitions and structural lemmas for Shortlex, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Shortlex.lean

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Data.List.Shortlex
public import Mathlib.Data.List.Lex
public import Mathlib.Data.Finset.Sort
public import Mathlib.Tactic
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset


set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification
variable {A : Type*} [Fintype A] [LinearOrder A]
def lexWords (n : ℕ) : List (Word A) := (allWords (A := A) n).sort
@[simp] theorem mem_lexWords {w : Word A} {n : ℕ} :
    w ∈ lexWords n ↔ w.length = n := by
  simp only [lexWords, Finset.mem_sort, mem_allWords]
def shortlexThrough (n : ℕ) : List (Word A) :=
  (List.range (n + 1)).flatMap (fun k => lexWords k)
@[simp] theorem mem_shortlexThrough {w : Word A} {n : ℕ} :
    w ∈ shortlexThrough n ↔ w.length ≤ n := by
  simp only [shortlexThrough, List.mem_flatMap, List.mem_range, mem_lexWords]
  constructor
  · rintro ⟨k, hk, hw⟩
    omega
  · intro hw
    exact ⟨w.length, by omega, rfl⟩
theorem shortlexThrough_succ (n : ℕ) :
    shortlexThrough (A := A) (n + 1) = shortlexThrough n ++ lexWords (n + 1) := by
  simp only [shortlexThrough, List.range_succ, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
variable [Nonempty A]
theorem lexWords_length_pos (n : ℕ) : 0 < (lexWords (A := A) n).length := by
  apply List.length_pos_iff.mpr
  intro hnil
  have hmem : List.replicate n (Classical.arbitrary A) ∈ lexWords n :=
    mem_lexWords.mpr (List.length_replicate ..)
  rw [hnil] at hmem
  exact List.not_mem_nil hmem
theorem shortlexThrough_length (n : ℕ) : n + 1 ≤ (shortlexThrough (A := A) n).length := by
  induction n with
  | zero =>
    have := lexWords_length_pos (A := A) 0
    simpa only [shortlexThrough, Nat.zero_add, List.range_one, List.flatMap_cons,
      List.flatMap_nil, List.append_nil] using (Nat.succ_le_of_lt this)
  | succ n ih =>
    have := lexWords_length_pos (A := A) (n + 1)
    rw [shortlexThrough_succ, List.length_append]
    omega
def shortlexWord (j : ℕ) : Word A :=
  (shortlexThrough (A := A) j)[j]'(by have := shortlexThrough_length (A := A) j; omega)
end BalanceSpecification



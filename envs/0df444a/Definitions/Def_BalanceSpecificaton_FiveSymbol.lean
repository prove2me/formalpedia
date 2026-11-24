-- Prove2me | Definitions.Def_BalanceSpecificaton_FiveSymbol
-- name    : BalanceSpecificaton_FiveSymbol
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:50:30.29982+00:00
-- url     : https://prove2.me/theorems/118e056d-f49e-47cc-9d6b-1bc2cc31a396
-- title:
--   Five Symbol
-- statement:
--   Definitions and structural lemmas for Five Symbol, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean

module
public import Definitions.Def_BalanceSpecificaton_Shortlex
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_shortlexWord_zero
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.shortlexWord_zero


set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification.FiveSymbol
abbrev Alphabet := Fin 5
instance : TopologicalSpace Alphabet := ⊥
instance : DiscreteTopology Alphabet := ⟨rfl⟩
def markerLength (j : ℕ) : ℕ := 5 ^ j
def markerLeft (j : ℕ) : Word Alphabet :=
  [0] ++ List.replicate (markerLength j) 1 ++ [2]
def markerRight (j : ℕ) : Word Alphabet :=
  [3] ++ List.replicate (markerLength j) 1 ++ [4]
def forbiddenWord (j : ℕ) : Word Alphabet :=
  markerLeft j ++ shortlexWord j ++ markerRight j
def forbiddenWords : Set (Word Alphabet) :=
  {f | ∃ j : ℕ, 1 ≤ j ∧ f = forbiddenWord j}
def shift : ShiftSpace Alphabet := forbiddenShift forbiddenWords
@[simp] theorem length_markerLeft (j : ℕ) :
    (markerLeft j).length = markerLength j + 2 := by
  simp only [markerLeft, List.length_append, List.length_singleton, List.length_replicate]
  omega
@[simp] theorem length_markerRight (j : ℕ) :
    (markerRight j).length = markerLength j + 2 := by
  simp only [markerRight, List.length_append, List.length_singleton, List.length_replicate]
  omega
@[simp] theorem length_forbiddenWord (j : ℕ) :
    (forbiddenWord j).length = 2 * markerLength j + (shortlexWord (A := Alphabet) j).length + 4 := by
  simp only [forbiddenWord, List.length_append, length_markerLeft, length_markerRight]
  omega
theorem forbiddenWord_length_pos (j : ℕ) : 0 < (forbiddenWord j).length := by
  rw [length_forbiddenWord]
  omega
def padded (w : Word Alphabet) : Configuration Alphabet := fun i =>
  if hneg : i < 0 then 4 else
    if hin : i < (w.length : ℤ) then w[i.toNat]'(by omega) else 0
def rightOffset (j : ℕ) : ℕ := (markerLeft j).length + (shortlexWord (A := Alphabet) j).length
@[simp] theorem forbiddenWord_length_rightOffset (j : ℕ) :
    (forbiddenWord j).length = rightOffset j + markerLength j + 2 := by
  simp only [rightOffset, length_markerLeft, length_forbiddenWord]
  omega
end BalanceSpecification.FiveSymbol



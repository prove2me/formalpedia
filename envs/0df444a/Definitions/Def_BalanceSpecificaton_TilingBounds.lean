-- Prove2me | Definitions.Def_BalanceSpecificaton_TilingBounds
-- name    : BalanceSpecificaton_TilingBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:37:11.495643+00:00
-- url     : https://prove2.me/theorems/35a454c5-016e-4477-b285-0a05ea973fc8
-- title:
--   Tiling Bounds
-- statement:
--   Definitions and structural lemmas for Tiling Bounds, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/TilingBounds.lean

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage


set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification
variable {A : Type*}
def interiorLanguage (L : Set (Word A)) (M : ℕ) : Set (Word A) :=
  {w | ∃ p q : Word A, M ≤ p.length ∧ M ≤ q.length ∧ p ++ w ++ q ∈ L}
theorem IsFactorial.interiorLanguage {L : Set (Word A)} (_hL : IsFactorial L) (M : ℕ) :
    IsFactorial (interiorLanguage L M) := by
  rintro u v ⟨a, b, rfl⟩ ⟨p, q, hp, hq, hword⟩
  refine ⟨p ++ a, b ++ q, ?_, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · simp only [List.length_append]
    omega
  · simpa only [List.append_assoc] using hword
variable [Fintype A]
end BalanceSpecification



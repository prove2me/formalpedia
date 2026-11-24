-- Prove2me | Definitions.Def_BalanceSpecificaton_SGap
-- name    : BalanceSpecificaton_SGap
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:38:18.757799+00:00
-- url     : https://prove2.me/theorems/3525973f-1a9b-44ec-96ae-c3684a1f5131
-- title:
--   SGap
-- statement:
--   Definitions and structural lemmas for SGap, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean

module
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Mathlib.Tactic
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_nil_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_periodicConfiguration_shift
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.nil_mem_generatedWords
attribute [local simp] BalanceSpecification.periodicConfiguration_shift
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BalanceSpecification
def sGapCode (S : Set ℕ) : Set (Word Bool) :=
  {w | ∃ s ∈ S, w = true :: List.replicate s false}
def sGapShift [TopologicalSpace Bool] (S : Set ℕ) : ShiftSpace Bool :=
  codedShift (sGapCode S)
inductive GapRead (S : Set ℕ) : ℕ → Word Bool → ℕ → Prop
  | nil (i : ℕ) : GapRead S i [] i
  | zero {i j : ℕ} {w : Word Bool} :
      GapRead S i w j → GapRead S (i + 1) (false :: w) j
  | one {s j : ℕ} {w : Word Bool} :
      s ∈ S → GapRead S s w j → GapRead S 0 (true :: w) j
def GapState (S : Set ℕ) (i : ℕ) : Prop := ∃ s ∈ S, i ≤ s
namespace GapRead
variable {S : Set ℕ} {a b c : ℕ} {u v : Word Bool}
end GapRead
namespace GapRead
variable {S : Set ℕ} {N a b : ℕ} {w : Word Bool}
end GapRead
def sGapPeriodic (s : ℕ) : Configuration Bool :=
  periodicConfiguration (true :: List.replicate s false) (by simp only [List.length_cons]; omega)
end BalanceSpecification



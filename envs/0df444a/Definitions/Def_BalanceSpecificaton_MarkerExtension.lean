-- Prove2me | Definitions.Def_BalanceSpecificaton_MarkerExtension
-- name    : BalanceSpecificaton_MarkerExtension
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:58:47.089531+00:00
-- url     : https://prove2.me/theorems/e1362bc2-ba2e-41f6-975d-6e0862c060ae
-- title:
--   Marker Extension
-- statement:
--   Definitions and structural lemmas for Marker Extension, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean

module
public import Definitions.Def_BalanceSpecificaton_MarkerEmbedding
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Theorems.Thm_BalanceSpecification_MarkerEmbedding_block_mapConfiguration
public import Theorems.Thm_BalanceSpecification_block_mem_language
public import Theorems.Thm_BalanceSpecification_codedShift_nonempty_iff
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
attribute [local simp] BalanceSpecification.MarkerEmbedding.block_mapConfiguration
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
noncomputable section
namespace BalanceSpecification.MarkerExtension
variable {A : Type*}
def markedCode (P : Set (Word A)) : Set (Word (Option A)) :=
  {z | ∃ v ∈ P, z = none :: v.map some}
variable [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
  [TopologicalSpace (Option A)] [DiscreteTopology (Option A)]
def PositiveLanguage (Y : ShiftSpace A) :=
  {u : Word A // u ∈ language Y ∧ 0 < u.length}
def sourceTail {Y : ShiftSpace A} (x : Y.carrier) (n : ℕ) : Word A :=
  block x.val (-(n : ℤ)) n
def suffixLength (M : ℕ) (s : ℕ → ℕ) (n : ℕ) : ℕ := s n - n - M
def sourceBridge {Y : ShiftSpace A} (M : ℕ)
    (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
      ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
    (x : Y.carrier) (s : ℕ → ℕ) (u : PositiveLanguage Y) : Word A :=
  Classical.choose (hM u.val u.property.1 (sourceTail x (suffixLength M s u.val.length))
    (block_mem_language x.property _ _))
def sourcePayload {Y : ShiftSpace A} (M : ℕ)
    (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
      ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
    (x : Y.carrier) (s : ℕ → ℕ) (u : PositiveLanguage Y) : Word A :=
  u.val ++ sourceBridge M hM x s u ++ sourceTail x (suffixLength M s u.val.length)
def code {Y : ShiftSpace A} (M : ℕ)
    (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
      ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
    (x : Y.carrier) (s : ℕ → ℕ) : Set (Word (Option A)) :=
  markedCode (Set.range (sourcePayload M hM x s))
def shift {Y : ShiftSpace A} (M : ℕ)
    (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
      ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
    (x : Y.carrier) (s : ℕ → ℕ) : ShiftSpace (Option A) := codedShift (code M hM x s)
omit [DiscreteTopology A] [Fintype A] [TopologicalSpace (Option A)] [DiscreteTopology (Option A)] in
theorem positiveLanguage_nonempty {Y : ShiftSpace A} (x : Y.carrier) :
    Nonempty (PositiveLanguage Y) :=
  ⟨block x.val 0 1, block_mem_language x.property 0 1, by simp only [length_block]; omega⟩
omit [DiscreteTopology A] [Fintype A] [TopologicalSpace (Option A)] [DiscreteTopology (Option A)] in
theorem code_nonempty_generator {Y : ShiftSpace A} (M : ℕ)
    (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
      ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
    (x : Y.carrier) (s : ℕ → ℕ) : ∃ z ∈ code M hM x s, 0 < z.length := by
  obtain ⟨u⟩ := positiveLanguage_nonempty x
  refine ⟨none :: (sourcePayload M hM x s u).map some, ?_, ?_⟩
  · exact ⟨sourcePayload M hM x s u, ⟨u, rfl⟩, rfl⟩
  · simp only [List.length_cons]
    omega
omit [DiscreteTopology A] [Fintype A] [DiscreteTopology (Option A)] in
theorem shift_nonempty {Y : ShiftSpace A} (M : ℕ)
    (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
      ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
    (x : Y.carrier) (s : ℕ → ℕ) : (shift M hM x s).carrier.Nonempty :=
  codedShift_nonempty_iff.mpr (code_nonempty_generator M hM x s)
section SourceCode
variable {Y : ShiftSpace A} (M : ℕ)
  (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
    ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
  (x : Y.carrier) (s : ℕ → ℕ)
end SourceCode
end BalanceSpecification.MarkerExtension



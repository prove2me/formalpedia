-- Prove2me | Definitions.Def_BalanceSpecificaton_MarkerCodeCounts
-- name    : BalanceSpecificaton_MarkerCodeCounts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:59:25.712584+00:00
-- url     : https://prove2.me/theorems/0c0b6e3a-a339-45f6-ad5c-ba4fb5ea5c07
-- title:
--   Marker Code Counts
-- statement:
--   Definitions and structural lemmas for Marker Code Counts, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerCodeCounts.lean

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Definitions.Def_BalanceSpecificaton_MarkerEstimates
public import Mathlib.Tactic
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
attribute [local simp] BalanceSpecification.mem_wordFinset


set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification.MarkerExtension
open scoped Classical
variable {A : Type*} [TopologicalSpace A] [Fintype A] {Y : ShiftSpace A}
variable (M : ℕ)
  (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
    ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
  (x : Y.carrier) (s : ℕ → ℕ)
def sourceCodeFinsetAt (n : ℕ) : Finset (Word (Option A)) := by
  classical
  let T := (wordFinset (language Y) n).filter (fun u => 0 < u.length)
  exact T.attach.image (fun u : ↥T =>
    let hu : u.val ∈ wordFinset (language Y) n ∧ 0 < u.val.length :=
      Finset.mem_filter.mp u.property
    none :: (sourcePayload M hM x s
      ⟨u.val, (mem_wordFinset.mp hu.1).1, hu.2⟩).map some)
end BalanceSpecification.MarkerExtension



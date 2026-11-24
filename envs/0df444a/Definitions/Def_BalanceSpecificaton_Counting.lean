-- Prove2me | Definitions.Def_BalanceSpecificaton_Counting
-- name    : BalanceSpecificaton_Counting
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:30:22.235849+00:00
-- url     : https://prove2.me/theorems/bae26781-4e64-48bc-871e-2aa07d3a4851
-- title:
--   Counting
-- statement:
--   Definitions and structural lemmas for Counting, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Counting.lean

module
public import Definitions.Def_BalanceSpecificaton_Language
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification
variable {A : Type*} [Fintype A]
def allWords (n : ℕ) : Finset (Word A) := by
  classical
  exact Finset.univ.image (fun f : Fin n → A => List.ofFn f)
def wordFinset (L : Set (Word A)) (n : ℕ) : Finset (Word A) := by
  classical
  exact (allWords n).filter (· ∈ L)
def wordCount (L : Set (Word A)) (n : ℕ) : ℕ := (wordFinset L n).card
def followerFinset (L : Set (Word A)) (u : Word A) (n : ℕ) : Finset (Word A) := by
  classical
  exact (wordFinset L n).filter (fun w => u ++ w ∈ L)
def predecessorFinset (L : Set (Word A)) (u : Word A) (n : ℕ) : Finset (Word A) := by
  classical
  exact (wordFinset L n).filter (fun w => w ++ u ∈ L)
def RightBalanced (L : Set (Word A)) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ u ∈ L, ∀ n : ℕ, 1 ≤ n →
    c ≤ ((followerFinset L u n).card : ℝ) / wordCount L n
def LeftBalanced (L : Set (Word A)) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ u ∈ L, ∀ n : ℕ, 1 ≤ n →
    c ≤ ((predecessorFinset L u n).card : ℝ) / wordCount L n
def BiBalanced (L : Set (Word A)) : Prop := RightBalanced L ∧ LeftBalanced L
def BoundedlySupermultiplicative (L : Set (Word A)) : Prop :=
  ∃ c : ℝ, 1 ≤ c ∧ ∀ m n : ℕ,
    (wordCount L m : ℝ) * wordCount L n ≤ c * wordCount L (m + n)
end BalanceSpecification



-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_02_def_2_1_F000
-- name    : ProbabilityTheory_chapter_02_def_2_1_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:55:00.809727+00:00
-- url     : https://prove2.me/theorems/55c83991-4f5a-4e5a-8a62-cd84442aa690
-- title:
--   Chapter 2, def_2_1: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 2, source module `def_2_1`: `SameCardinality`, `IsCountableSet`, `IsAtMostCountableSet`, `IsUncountableSet`, `def_2_1`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/def_2_1.lean

import Mathlib.Tactic

open Set

noncomputable section countable_set

def SameCardinality {α β : Type*} (A : Set α) (B : Set β) : Prop :=
  Nonempty (A ≃ B)

def IsCountableSet {α : Type*} (A : Set α) : Prop :=
  SameCardinality A (Set.univ : Set ℕ)

def IsAtMostCountableSet {α : Type*} (A : Set α) : Prop :=
  A.Countable

def IsUncountableSet {α : Type*} (A : Set α) : Prop :=
  A.Infinite ∧ ¬ IsCountableSet A

def def_2_1 {α : Type*} (A : Set α) : Prop :=
  IsCountableSet A
end countable_set



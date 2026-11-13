-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_02_def_2_2_F000
-- name    : ProbabilityTheory_chapter_02_def_2_2_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:55:08.487918+00:00
-- url     : https://prove2.me/theorems/47050360-68c0-4c2a-8af6-d684619ec92e
-- title:
--   Chapter 2, def_2_2: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 2, source module `def_2_2`: `EventAlgebra`, `IsEvent`, `def_2_2`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/def_2_2.lean

import Mathlib.Tactic

open Set

structure EventAlgebra (Ω : Type*) where
  carrier : Set (Set Ω)
  univ_mem : Set.univ ∈ carrier
  union_mem : ∀ {A B : Set Ω}, A ∈ carrier → B ∈ carrier → A ∪ B ∈ carrier
  compl_mem : ∀ {A : Set Ω}, A ∈ carrier → Aᶜ ∈ carrier

def IsEvent {Ω : Type*} (𝓕 : EventAlgebra Ω) (A : Set Ω) : Prop :=
  A ∈ 𝓕.carrier

def def_2_2 (Ω : Type*) : Type _  :=
  EventAlgebra Ω



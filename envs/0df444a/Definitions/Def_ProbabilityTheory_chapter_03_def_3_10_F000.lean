-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_03_def_3_10_F000
-- name    : ProbabilityTheory_chapter_03_def_3_10_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:57:08.748784+00:00
-- url     : https://prove2.me/theorems/e2c87726-d3ae-4853-87c2-548abf8ae165
-- title:
--   Chapter 3, def_3_10: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 3, source module `def_3_10`: `PiSystem`, `LambdaSystem`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_03/def_3_10.lean

import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.MeasureTheory.PiSystem

open Set

variable {Ω : Type*}

def PiSystem {Ω : Type*} (P : Set (Set Ω)) : Prop :=
  P.Nonempty ∧ ∀ ⦃A⦄, A ∈ P → ∀ ⦃B⦄, B ∈ P → A ∩ B ∈ P

structure LambdaSystem (L : Set (Set Ω)) : Prop where

  univ_mem : univ ∈ L

  compl_mem : ∀ {A}, A ∈ L → Aᶜ ∈ L

  iUnion_mem : ∀ {f : ℕ → Set Ω}, Pairwise (fun i j => Disjoint (f i) (f j))
    → (∀ i, f i ∈ L) → (⋃ i, f i) ∈ L



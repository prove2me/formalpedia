-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_03_def_3_7_F000
-- name    : ProbabilityTheory_chapter_03_def_3_7_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:57:50.778307+00:00
-- url     : https://prove2.me/theorems/f5e34157-bae3-4283-b157-fdd1b8a2a7fb
-- title:
--   Chapter 3, def_3_7: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 3, source module `def_3_7`: `IsOpenCover`, `IsSubcover`, `IsFiniteCover`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_03/def_3_7.lean

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic

open Set

variable {X : Type*} [TopologicalSpace X]

def IsOpenCover (A : Set X) {ι : Type*} (u : ι → Set X) : Prop :=
  (∀ i, IsOpen (u i)) ∧ A ⊆ ⋃ i, u i

def IsSubcover (A : Set X) {ι : Type*} (u : ι → Set X) (J : Set ι) : Prop :=
  IsOpenCover A (fun (j : J) => u j)

def IsFiniteCover (A : Set X) {ι : Type*} (u : ι → Set X) : Prop :=
  IsOpenCover A u ∧ Finite ι



-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_02_def_2_4_F000
-- name    : ProbabilityTheory_chapter_02_def_2_4_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:55:34.104256+00:00
-- url     : https://prove2.me/theorems/7488ec2c-74d4-4352-b0a6-d44aad1dac0e
-- title:
--   Chapter 2, def_2_4: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 2, source module `def_2_4`: `setLiminf`, `setLimsup`, `setSeqLimitExists`, `setLiminf_subset_setLimsup`, `def_2_4`, and 1 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/def_2_4.lean

import Mathlib.Tactic

open Set

def setLiminf {Ω : Type*} (E : ℕ → Set Ω) : Set Ω :=
  ⋃ n : ℕ, ⋂ m ∈ Set.Ici n, E m

def setLimsup {Ω : Type*} (E : ℕ → Set Ω) : Set Ω :=
  ⋂ n : ℕ, ⋃ m ∈ Set.Ici n, E m

def setSeqLimitExists {Ω : Type*} (E : ℕ → Set Ω) : Prop :=
  setLiminf E = setLimsup E



def def_2_4 {Ω : Type*} (E : ℕ → Set Ω)
    (_h : setSeqLimitExists E) : Set Ω :=
  setLiminf E



-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_02_def_2_6_F000
-- name    : ProbabilityTheory_chapter_02_def_2_6_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:55:50.696593+00:00
-- url     : https://prove2.me/theorems/75f3d9f0-2669-4a65-9049-8d304cab9a1c
-- title:
--   Chapter 2, def_2_6: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 2, source module `def_2_6`: `SetSeqIncreasing`, `SetSeqDecreasing`, `def_2_6`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/def_2_6.lean

import Mathlib.Tactic

open Set

def SetSeqIncreasing {Ω : Type*} (A : ℕ → Set Ω) : Prop :=
  Monotone A

def SetSeqDecreasing {Ω : Type*} (A : ℕ → Set Ω) : Prop :=
  Antitone A

def def_2_6 {Ω : Type*} (A : ℕ → Set Ω) : Prop :=
  SetSeqIncreasing A



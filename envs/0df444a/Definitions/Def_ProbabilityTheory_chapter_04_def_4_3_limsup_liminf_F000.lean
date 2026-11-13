-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_04_def_4_3_limsup_liminf_F000
-- name    : ProbabilityTheory_chapter_04_def_4_3_limsup_liminf_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:59:23.778461+00:00
-- url     : https://prove2.me/theorems/ce007088-4b75-41d5-9270-88d1c2695cc8
-- title:
--   Chapter 4, def_4_3_limsup_liminf: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 4, source module `def_4_3_limsup_liminf`: `tailSup`, `tailInf`, `seqLimsup`, `seqLiminf`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_04/def_4_3_limsup_liminf.lean

import Definitions.Def_ProbabilityTheory_chapter_04_def_4_3_sup_inf_F000
import Mathlib.Tactic

noncomputable def tailSup {α : Type*} [CompleteLattice α] (a : ℕ → α) (n : ℕ) : α :=
  ⨆ k : ℕ, a (n + k)

noncomputable def tailInf {α : Type*} [CompleteLattice α] (a : ℕ → α) (n : ℕ) : α :=
  ⨅ k : ℕ, a (n + k)

noncomputable def seqLimsup {α : Type*} [CompleteLattice α] (a : ℕ → α) : α :=
  ⨅ n : ℕ, tailSup a n

noncomputable def seqLiminf {α : Type*} [CompleteLattice α] (a : ℕ → α) : α :=
  ⨆ n : ℕ, tailInf a n



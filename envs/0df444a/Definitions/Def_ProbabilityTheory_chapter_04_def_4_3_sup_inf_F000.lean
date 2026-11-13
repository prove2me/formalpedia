-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_04_def_4_3_sup_inf_F000
-- name    : ProbabilityTheory_chapter_04_def_4_3_sup_inf_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:59:09.902233+00:00
-- url     : https://prove2.me/theorems/9a386f0f-711b-4343-9982-08cb326467d1
-- title:
--   Chapter 4, def_4_3_sup_inf: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 4, source module `def_4_3_sup_inf`: `IsSupremum`, `IsInfimum`, `seqSup`, `seqInf`, `setSupEReal`, and 1 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_04/def_4_3_sup_inf.lean

import Mathlib.Tactic

open Set

abbrev IsSupremum (A : Set ℝ) (r : ℝ) : Prop :=
  IsLUB A r

abbrev IsInfimum (A : Set ℝ) (s : ℝ) : Prop :=
  IsGLB A s

noncomputable def seqSup {α : Type*} [CompleteLattice α] (a : ℕ → α) : α :=
  iSup a

noncomputable def seqInf {α : Type*} [CompleteLattice α] (a : ℕ → α) : α :=
  iInf a

noncomputable def setSupEReal (A : Set ℝ) : EReal :=
  sSup ((fun x : ℝ => (x : EReal)) '' A)

noncomputable def setInfEReal (A : Set ℝ) : EReal :=
  sInf ((fun x : ℝ => (x : EReal)) '' A)



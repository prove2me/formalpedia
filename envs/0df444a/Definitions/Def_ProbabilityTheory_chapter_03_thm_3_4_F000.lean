-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_03_thm_3_4_F000
-- name    : ProbabilityTheory_chapter_03_thm_3_4_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:58:28.52635+00:00
-- url     : https://prove2.me/theorems/bed1fb30-fd83-470f-9693-0911f1d005ab
-- title:
--   Chapter 3, thm_3_4: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 3, source module `thm_3_4`: `IsCompactTextbook`, `heine_borel`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_03/thm_3_4.lean

import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Bounded

open Set Metric Bornology

def IsCompactTextbook (A : Set ℝ) : Prop :=
  IsClosed A ∧ IsBounded A



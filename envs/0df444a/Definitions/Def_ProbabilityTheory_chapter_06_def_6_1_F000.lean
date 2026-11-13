-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_06_def_6_1_F000
-- name    : ProbabilityTheory_chapter_06_def_6_1_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T08:01:46.328309+00:00
-- url     : https://prove2.me/theorems/713e7605-8059-4227-8d14-7b94a819f624
-- title:
--   Chapter 6, def_6_1: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 6, source module `def_6_1`: `SimpleFunction`, `def_6_1`, `measurable_of_simpleFunction`, `finite_range_of_simpleFunction`, `measurableSet_fiber`, and 3 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/def_6_1.lean

import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

open MeasureTheory
open scoped BigOperators

abbrev SimpleFunction (Ω : Type*) [MeasurableSpace Ω] : Type _ :=
  MeasureTheory.SimpleFunc Ω EReal

def def_6_1 (Ω : Type*) [MeasurableSpace Ω] : Type _ :=
  SimpleFunction Ω
namespace SimpleFunction

variable {Ω : Type*} [MeasurableSpace Ω]












end SimpleFunction



-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_03_def_3_5_F000
-- name    : ProbabilityTheory_chapter_03_def_3_5_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:57:34.865117+00:00
-- url     : https://prove2.me/theorems/f0b1be66-9fe6-4204-a8b8-eb596599ad5f
-- title:
--   Chapter 3, def_3_5: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 3, source module `def_3_5`: `StieltjesMeasureFunction`, `StieltjesMeasureFunction.toStieltjesFunction`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_03/def_3_5.lean

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Topology.Order.Basic

open Set Filter

structure StieltjesMeasureFunction where

  toFun : ℝ → ℝ

  non_decreasing : Monotone toFun

  right_continuous : ∀ x : ℝ, ContinuousWithinAt toFun (Ici x) x

instance : CoeFun StieltjesMeasureFunction (fun _ => ℝ → ℝ) where
  coe F := F.toFun

def StieltjesMeasureFunction.toStieltjesFunction (F : StieltjesMeasureFunction) :
    StieltjesFunction ℝ where
  toFun := F.toFun
  mono' := F.non_decreasing
  right_continuous' := F.right_continuous



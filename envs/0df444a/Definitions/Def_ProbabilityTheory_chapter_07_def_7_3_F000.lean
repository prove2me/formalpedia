-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_07_def_7_3_F000
-- name    : ProbabilityTheory_chapter_07_def_7_3_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T15:27:01.541576+00:00
-- url     : https://prove2.me/theorems/16045760-62df-44b4-b769-eaf7f16c367b
-- title:
--   Chapter 7, def_7_3: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 7, source module `def_7_3`: `Uncorrelated`, `Covariance`, `covariance_zero_iff_uncorrelated`, `independent_uncorrelated`, `def_7_3`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_07/def_7_3.lean

import Definitions.Def_ProbabilityTheory_chapter_05_def_5_2_F000
import Definitions.Def_ProbabilityTheory_chapter_07_thm_7_13_F000
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Covariance
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory

def Uncorrelated {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X Y : Ω → ℝ) : Prop :=
  ∫ ω, X ω * Y ω ∂μ = (∫ ω, X ω ∂μ) * ∫ ω, Y ω ∂μ

noncomputable def Covariance {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X Y : Ω → ℝ) : ℝ :=
  ProbabilityTheory.covariance X Y μ





def def_7_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X Y : Ω → ℝ) : Prop :=
  Uncorrelated μ X Y



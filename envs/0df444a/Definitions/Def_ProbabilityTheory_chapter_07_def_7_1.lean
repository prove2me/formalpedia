-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_07_def_7_1
-- name    : ProbabilityTheory_chapter_07_def_7_1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T08:02:56.899754+00:00
-- url     : https://prove2.me/theorems/b1c159be-2080-4890-852b-20ea379ccc13
-- title:
--   Chapter ?, generated supplement: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter ?, source module `generated supplement`: `EqualEverywhere`, `EqualAlmostEverywhere`, `EquivalentFunctions`, `def_7_1`. The mathematical interpretation of this bundle needs review.
-- source:
--   Supplemental source module in importer v37; upstream repository https://github.com/wkshum/ProbabilityTheory/tree/e6387d4fd8005d627d2aec40d10f039ddb4e4b40

import Mathlib.Tactic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

open MeasureTheory Set

def EqualEverywhere {Ω E : Type*} (f g : Ω → E) : Prop :=
  ∀ ω, f ω = g ω

def EqualAlmostEverywhere {Ω E : Type*}
  [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → E) : Prop :=
  ∃ A : Set Ω, MeasurableSet A ∧ μ A = 0 ∧ EqOn f g Aᶜ

def EquivalentFunctions {Ω E : Type*}
  [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → E) : Prop :=
  EqualAlmostEverywhere μ f g

def def_7_1 {Ω E : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) (f g : Ω → E) :
    Prop :=
  EquivalentFunctions μ f g



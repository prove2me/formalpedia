-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_08_def_8_1_F000
-- name    : ProbabilityTheory_chapter_08_def_8_1_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:38:54.532197+00:00
-- url     : https://prove2.me/theorems/8111d7a5-5eb0-4c49-913f-4527d583be3c
-- title:
--   Definition 8.1: Coupling of probability measures
-- statement:
--   A coupling of two probability measures is a common probability space carrying two measurable random variables whose push-forward laws are the prescribed measures.
-- source:
--   Kenneth W. Shum (2023), Definition 8.1: Coupling of probability measures, Lean source: https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_08/def_8_1.lean

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

open MeasureTheory

structure Coupling
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure α) (Q : Measure β) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] where
  Ω : Type*
  instMeasurableSpaceΩ : MeasurableSpace Ω
  μ : Measure Ω
  instIsProbabilityMeasureμ : IsProbabilityMeasure μ
  X : Ω → α
  Y : Ω → β
  measurable_X : Measurable X
  measurable_Y : Measurable Y
  map_X : Measure.map X μ = P
  map_Y : Measure.map Y μ = Q
attribute [instance] Coupling.instMeasurableSpaceΩ Coupling.instIsProbabilityMeasureμ

noncomputable def def_8_1
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure α) (Q : Measure β) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :=
  Coupling P Q



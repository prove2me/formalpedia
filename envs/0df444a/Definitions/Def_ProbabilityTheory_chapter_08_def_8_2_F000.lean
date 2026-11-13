-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_08_def_8_2_F000
-- name    : ProbabilityTheory_chapter_08_def_8_2_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T08:03:18.041393+00:00
-- url     : https://prove2.me/theorems/158ce9c1-f941-4bae-92b8-86711a094515
-- title:
--   Chapter 8, def_8_2: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 8, source module `def_8_2`: `DeterministicCoupling`, `TransportMap`, `def_8_2`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_08/def_8_2.lean

import Definitions.Def_ProbabilityTheory_chapter_08_def_8_1_F000
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

open MeasureTheory

structure DeterministicCoupling
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure α) (Q : Measure β) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    extends Coupling P Q where
  T : α → β
  measurable_T : Measurable T
  Y_eq_transport : Y = T ∘ X

noncomputable def TransportMap
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {P : Measure α} {Q : Measure β} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (π : DeterministicCoupling P Q) : α → β :=
  π.T

noncomputable def def_8_2
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure α) (Q : Measure β) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :=
  DeterministicCoupling P Q



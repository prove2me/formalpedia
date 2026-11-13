-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_08_def_8_3_F000
-- name    : ProbabilityTheory_chapter_08_def_8_3_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T08:03:26.354797+00:00
-- url     : https://prove2.me/theorems/a8189c6a-d72d-4ca3-a0fd-208e717fc5e7
-- title:
--   Chapter 8, def_8_3: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 8, source module `def_8_3`: `MeasurableRectangle`, `MeasurableRectangles`, `ProductSigmaField`, `measurableRectangle_measurable`, `def_8_3`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_08/def_8_3.lean

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Tactic

open Set

def MeasurableRectangle
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (E₁ : Set α) (E₂ : Set β) : Set (α × β) :=
  E₁ ×ˢ E₂

def MeasurableRectangles
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] : Set (Set (α × β)) :=
  {s | ∃ E₁ : Set α, ∃ E₂ : Set β, MeasurableSet E₁ ∧ MeasurableSet E₂ ∧
      s = MeasurableRectangle E₁ E₂}

@[reducible]
def ProductSigmaField
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] : MeasurableSpace (α × β) :=
  inferInstance



@[reducible]
def def_8_3
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] : MeasurableSpace (α × β) :=
  ProductSigmaField



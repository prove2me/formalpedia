-- Prove2me | Definitions.Def_ChapterProbabilityInterface
-- name    : ChapterProbabilityInterface
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:37:34.77696+00:00
-- url     : https://prove2.me/theorems/6b2d4ecf-23e4-4746-ac86-8250cd2d1b65
-- title:
--   Chapter ProbabilityInterface
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterProbabilityInterface.lean`): generated def bundle for ChapterProbabilityInterface. See BookProof/ChapterProbabilityInterface.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterProbabilityInterface.lean

import Mathlib


/-!
# Probability as an interface between measurable theories

A measurable equivalence transports a probability law by `Measure.map`; the
inverse transports it back.  This gives a rigorous form of translation between
isomorphic standard measurable presentations without claiming that arbitrary
unrelated standard probability spaces are isomorphic.
-/

open MeasureTheory

namespace BookProof.ChapterProbabilityInterface

/-- Transport a law across a measurable equivalence. -/
noncomputable def transportMeasure {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (e : X ≃ᵐ Y) (μ : Measure X) : Measure Y :=
  Measure.map e μ







end BookProof.ChapterProbabilityInterface



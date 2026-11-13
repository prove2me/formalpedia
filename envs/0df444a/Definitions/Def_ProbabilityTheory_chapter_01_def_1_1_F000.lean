-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_def_1_1_F000
-- name    : ProbabilityTheory_chapter_01_def_1_1_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:39:32.710195+00:00
-- url     : https://prove2.me/theorems/cf2c1128-edc8-4873-8ff0-a086d52ed69e
-- title:
--   Definition 1.1: Singular random variables
-- statement:
--   A real-valued random variable is singular when its law is concentrated on a Lebesgue-null set. The same source module defines singular random vectors.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/def_1_1.lean

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

open MeasureTheory Set

def IsSingularRealRandomVariable {Ω : Type*}
  [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) :
    Prop :=
  ∃ S : Set ℝ, volume S = 0 ∧ P (X ⁻¹' S) = 1

def IsSingularRandomVector {Ω : Type*}
  [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : Ω → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ S : Set (EuclideanSpace ℝ (Fin n)), volume S = 0 ∧ P (X ⁻¹' S) = 1

def def_1_1 {Ω : Type*}
  [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) : Prop :=
  IsSingularRealRandomVariable P X



-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_05_def_5_5to10_F000
-- name    : ProbabilityTheory_chapter_05_def_5_5to10_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T08:01:27.381742+00:00
-- url     : https://prove2.me/theorems/daf7af80-e0e4-4aed-8931-21c031f1a9d0
-- title:
--   Chapter 5, def_5_5to10: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter 5, source module `def_5_5to10`: `def_5_5`, `def_5_6`, `def_5_7`, `def_5_8`, `def_5_9`, and 2 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_05/def_5_5to10.lean

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic

def def_5_5 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) {n : ℕ}
    (A : Fin n → Set Ω) : Prop :=
  ProbabilityTheory.iIndepSet A μ

def def_5_6 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) {n : ℕ}
    (A : Fin n → Set Ω) : Prop :=
  Pairwise (fun i j => ProbabilityTheory.IndepSet (A i) (A j) μ)

def def_5_7 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) {n : ℕ}
    (F : Fin n → Set (Set Ω)) : Prop :=
  ProbabilityTheory.iIndepSets F μ

def def_5_8 {Ω β : Type _} [MeasurableSpace Ω] [MeasurableSpace β] (μ : MeasureTheory.Measure Ω) {n : ℕ}
    (X : Fin n → Ω → β) : Prop :=
  ProbabilityTheory.iIndepFun X μ

def def_5_9 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (F : ℕ → Set (Set Ω)) : Prop :=
  ProbabilityTheory.iIndepSets F μ

def def_5_10 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (A : ℕ → Set Ω) : Prop :=
  ProbabilityTheory.iIndepSet A μ

def def_5_10_randomVariables {Ω β : Type _} [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : MeasureTheory.Measure Ω) (X : ℕ → Ω → β) : Prop :=
  ProbabilityTheory.iIndepFun X μ



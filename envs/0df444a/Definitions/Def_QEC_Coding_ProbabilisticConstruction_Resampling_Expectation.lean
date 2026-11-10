-- Prove2me | Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Expectation
-- name    : QEC_Coding_ProbabilisticConstruction_Resampling_Expectation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T19:25:36.698527+00:00
-- url     : https://prove2.me/theorems/da1a4d56-2e9e-48a8-8cff-7bf69bc675f2
-- title:
--   Expectation
-- statement:
--   Definitions and structural lemmas for Expectation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Expectation.lean

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_OccurrenceCounting
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
set_option autoImplicit false
namespace QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable [MeasurableSpace I] [MeasurableSingletonClass I]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
variable (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
variable (hbad : ∀ i, MeasurableSet (bad i))
variable (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
variable (hcrit : ∀ i, eventProbability vars ν bad i ≤
  x i * ∏ j ∈ (supportGraph vars).neighborFinset i, (1 - x j))
noncomputable def totalCount (R : Table (X := X)) (i : I) : ℝ≥0∞ :=
  ⨆ T : ℕ, (prefixCount vars bad R T i : ℝ≥0∞)
noncomputable def totalSteps (R : Table (X := X)) : ℝ≥0∞ :=
  ∑ i, totalCount vars bad R i
end QEC.Coding.ProbabilisticConstruction.Resampling



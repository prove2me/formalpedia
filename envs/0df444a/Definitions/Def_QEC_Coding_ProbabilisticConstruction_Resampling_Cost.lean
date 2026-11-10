-- Prove2me | Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Cost
-- name    : QEC_Coding_ProbabilisticConstruction_Resampling_Cost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T19:27:20.474962+00:00
-- url     : https://prove2.me/theorems/18ab2e6f-ad74-42a9-abc9-15679d5cf0d1
-- title:
--   Cost
-- statement:
--   Definitions and structural lemmas for Cost, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Cost.lean

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
set_option autoImplicit false
namespace QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
section Scan
variable {Ω I : Type*} (B : I → Set Ω) [∀ i, DecidablePred (· ∈ B i)]
def scanCost (queryCost : I → ℝ≥0∞) : List I → Ω → ℝ≥0∞
  | [], _ => 0
  | i :: tail, ω => queryCost i + if ω ∈ B i then 0 else scanCost queryCost tail ω
end Scan
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
def executionScanCost (queryCost : I → ℝ≥0∞) (R : Table (X := X)) (n : ℕ) : ℝ≥0∞ :=
  scanCost (localEvent vars bad) queryCost (Finset.univ.sort (· ≤ ·))
    (assignment R (counters vars bad R n))
noncomputable def executionRefreshCost (sampleCost : V → ℝ≥0∞) (R : Table (X := X)) (n : ℕ) : ℝ≥0∞ :=
  match selected vars bad R n with
  | none => 0
  | some i => ∑ v ∈ vars i, sampleCost v
open scoped Classical in
/-- Cost of the actual run, with infinity for nontermination. -/
noncomputable def executionCost (queryCost : I → ℝ≥0∞) (sampleCost : V → ℝ≥0∞)
    (outputCost : ℝ≥0∞) (R : Table (X := X)) : ℝ≥0∞ :=
  if Halts vars bad R then
    (∑ v, sampleCost v) + outputCost +
      (∑ n ∈ Finset.range (haltTime vars bad R + 1), executionScanCost vars bad queryCost R n) +
      ∑ n ∈ Finset.range (haltTime vars bad R), executionRefreshCost vars bad sampleCost R n
  else ∞
variable [MeasurableSpace I] [MeasurableSingletonClass I]
variable (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
variable (hbad : ∀ i, MeasurableSet (bad i))
variable (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
variable (hcrit : ∀ i, eventProbability vars ν bad i ≤
  x i * ∏ j ∈ (supportGraph vars).neighborFinset i, (1 - x j))
end QEC.Coding.ProbabilisticConstruction.Resampling



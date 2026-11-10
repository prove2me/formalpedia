-- Prove2me | Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
-- name    : QEC_Coding_ProbabilisticConstruction_Resampling_Termination
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T19:26:18.297228+00:00
-- url     : https://prove2.me/theorems/8ee89ea9-fcf6-49e6-80b2-ee92c066e8da
-- title:
--   Termination
-- statement:
--   Definitions and structural lemmas for Termination, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Termination.lean

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Expectation
set_option autoImplicit false
namespace QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
def Halts (R : Table (X := X)) : Prop := ∃ n, selected vars bad R n = none
noncomputable def haltTime (R : Table (X := X)) : ℕ := by
  classical
  exact if h : Halts vars bad R then Nat.find h else 0
noncomputable def output (R : Table (X := X)) : ∀ v, X v :=
  assignment R (counters vars bad R (haltTime vars bad R))
variable [MeasurableSpace I] [MeasurableSingletonClass I]
variable (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
variable (hbad : ∀ i, MeasurableSet (bad i))
variable (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
variable (hcrit : ∀ i, eventProbability vars ν bad i ≤
  x i * ∏ j ∈ (supportGraph vars).neighborFinset i, (1 - x j))
end QEC.Coding.ProbabilisticConstruction.Resampling



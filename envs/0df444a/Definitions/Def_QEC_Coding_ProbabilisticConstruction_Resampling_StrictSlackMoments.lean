-- Prove2me | Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_StrictSlackMoments
-- name    : QEC_Coding_ProbabilisticConstruction_Resampling_StrictSlackMoments
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T19:36:58.094063+00:00
-- url     : https://prove2.me/theorems/641c815e-5994-4422-aa55-3092929443ec
-- title:
--   Strict Slack Moments
-- statement:
--   Definitions and structural lemmas for Strict Slack Moments, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/StrictSlackMoments.lean

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Expectation
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.GeomSum
set_option autoImplicit false
namespace QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable def momentWeight (D : ℕ) : ℝ := 1 / (2 * ((D : ℝ) + 1))
noncomputable def momentRatio (D : ℕ) : ℝ := ((D : ℝ) + 1) / ((D : ℝ) + 2)
section Trees
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]
def pathCount (h : ℕ) (i : I) (t : WitnessTree G h i) : ℕ :=
  (witnessPaths G h i t).card
end Trees
section Execution
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
variable [MeasurableSpace I] [MeasurableSingletonClass I]
variable (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
variable (hbad : ∀ i, MeasurableSet (bad i))
end Execution
end QEC.Coding.ProbabilisticConstruction.Resampling



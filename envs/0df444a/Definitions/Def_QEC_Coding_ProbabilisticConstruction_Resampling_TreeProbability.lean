-- Prove2me | Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TreeProbability
-- name    : QEC_Coding_ProbabilisticConstruction_Resampling_TreeProbability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T19:22:15.887973+00:00
-- url     : https://prove2.me/theorems/108b3d9b-b968-4a9f-8434-de1c1d129478
-- title:
--   Tree Probability
-- statement:
--   Definitions and structural lemmas for Tree Probability, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/TreeProbability.lean

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ExecutionWitness
import Mathlib.Data.ENNReal.BigOperators
set_option autoImplicit false
namespace QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
variable (bad : ∀ i, Set (∀ v : vars i, X v))
noncomputable def eventProbability (i : I) : ℝ :=
  ((Measure.pi ν) (localEvent vars bad i)).toReal
end QEC.Coding.ProbabilisticConstruction.Resampling



-- Prove2me | Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessCompatibility
-- name    : QEC_Coding_ProbabilisticConstruction_Resampling_WitnessCompatibility
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T19:18:41.612192+00:00
-- url     : https://prove2.me/theorems/3fbcaa41-ccf2-45da-ad3f-7a7a04aa4214
-- title:
--   Witness Compatibility
-- statement:
--   Definitions and structural lemmas for Witness Compatibility, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/WitnessCompatibility.lean

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryTimes
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
set_option autoImplicit false
namespace QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
variable (vars : I → Finset V)
def DistinctVariableDepth (root : I) (P : Finset (List I)) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, ∀ v ∈ vars (pathLabel root p),
    v ∈ vars (pathLabel root q) → p.length = q.length → p = q
def variableRank (root : I) (P : Finset (List I)) (p : List I) (v : V) : ℕ :=
  (P.filter (fun q => v ∈ vars (pathLabel root q) ∧ p.length < q.length)).card
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
variable (bad : ∀ i, Set (∀ v : vars i, X v))
def compatible (root : I) (P : Finset (List I)) : Set (Table (X := X)) :=
  {R | DistinctVariableDepth vars root P ∧
    ∀ p : P, familyRead (fun q : P => vars (pathLabel root q.val))
      (fun q v => variableRank vars root P q.val v.val) R p ∈ bad (pathLabel root p.val)}
end QEC.Coding.ProbabilisticConstruction.Resampling



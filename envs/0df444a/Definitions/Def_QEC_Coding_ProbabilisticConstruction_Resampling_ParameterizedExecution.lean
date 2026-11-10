-- Prove2me | Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ParameterizedExecution
-- name    : QEC_Coding_ProbabilisticConstruction_Resampling_ParameterizedExecution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T22:31:54.400994+00:00
-- url     : https://prove2.me/theorems/68f3587c-bc00-465d-b52d-0545f8e2e119
-- title:
--   Parameterized Execution
-- statement:
--   Definitions and structural lemmas for Parameterized Execution, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/ParameterizedExecution.lean

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
set_option autoImplicit false
namespace QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
section ParameterizedScan
variable {A W I : Type*} [MeasurableSpace A] [MeasurableSpace W]
variable [Fintype I] [LinearOrder I] [MeasurableSpace I]
variable (B : A → I → Set W) [∀ a i, DecidablePred (· ∈ B a i)]
end ParameterizedScan
section OrderConjugacy
variable {W I K : Type*} [Fintype I] [LinearOrder I] [Fintype K] [LinearOrder K]
variable (B : I → Set W) (C : K → Set W)
variable [∀ i, DecidablePred (· ∈ B i)] [∀ k, DecidablePred (· ∈ C k)]
end OrderConjugacy
section ParameterizedExecution
variable {A V I : Type*} [MeasurableSpace A]
variable [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
variable [MeasurableSpace I] [MeasurableSingletonClass I]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : A → ∀ i, Set (∀ v : vars i, X v))
variable [∀ a i, DecidablePred (· ∈ bad a i)]
variable (hbad : ∀ i, MeasurableSet
  {z : A × (∀ v : vars i, X v) | z.2 ∈ bad z.1 i})
end ParameterizedExecution
end QEC.Coding.ProbabilisticConstruction.Resampling



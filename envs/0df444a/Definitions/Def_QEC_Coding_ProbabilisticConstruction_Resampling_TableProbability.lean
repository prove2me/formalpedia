-- Prove2me | Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
-- name    : QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:08:54.078187+00:00
-- url     : https://prove2.me/theorems/3a535591-4678-4033-8888-431f3e64f54b
-- title:
--   Table Probability
-- statement:
--   Definitions and structural lemmas for Table Probability, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/TableProbability.lean

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution
import Mathlib.Probability.Independence.InfinitePi
set_option autoImplicit false
namespace QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
def familyRead (coords : A → Finset V) (column : ∀ a, coords a → ℕ)
    (R : Table (X := X)) (a : A) (v : coords a) : X v := R (v, column a v)
end QEC.Coding.ProbabilisticConstruction.Resampling



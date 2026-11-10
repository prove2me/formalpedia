-- Prove2me | Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ExecutionWitness
-- name    : QEC_Coding_ProbabilisticConstruction_Resampling_ExecutionWitness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T19:21:11.294696+00:00
-- url     : https://prove2.me/theorems/6d3843d1-9ffe-4efa-91d0-5849c1b31aae
-- title:
--   Execution Witness
-- statement:
--   Definitions and structural lemmas for Execution Witness, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/ExecutionWitness.lean

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryCounters
import Mathlib.Data.List.OfFn
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_halt_absorbing

set_option autoImplicit false
namespace QEC.Coding.ProbabilisticConstruction.Resampling
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
theorem selected_some_before (R : Table (X := X)) (n : ℕ) (i : I)
    (hi : selected vars bad R n = some i) (k : ℕ) (hk : k ≤ n) :
    ∃ j, selected vars bad R k = some j := by
  cases he : selected vars bad R k with
  | some j => exact ⟨j, rfl⟩
  | none =>
    have hn := (halt_absorbing vars bad R k he (n - k)).2
    rw [Nat.add_sub_of_le hk, hi] at hn
    cases hn
noncomputable def occurrenceHistory (R : Table (X := X)) (n : ℕ) (i : I)
    (hi : selected vars bad R n = some i) : List I :=
  List.ofFn (fun k : Fin n => Classical.choose
    (selected_some_before vars bad R n i hi k.val (Nat.le_of_lt k.isLt)))
end QEC.Coding.ProbabilisticConstruction.Resampling



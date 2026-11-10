-- Prove2me | Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryCounters
-- name    : QEC_Coding_ProbabilisticConstruction_Resampling_HistoryCounters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T19:20:07.996812+00:00
-- url     : https://prove2.me/theorems/91c326d3-3f69-49b6-be83-7aefc0fa9aa4
-- title:
--   History Counters
-- statement:
--   Definitions and structural lemmas for History Counters, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryCounters.lean

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessCompatibility
set_option autoImplicit false
namespace QEC.Coding.ProbabilisticConstruction.Resampling
variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
variable (vars : I → Finset V)
def historyCounter (root : I) (L : List I) (n : ℕ) (v : V) : ℕ :=
  ((Finset.range n).filter (fun k => v ∈ vars (historyLabel root L k))).card
end QEC.Coding.ProbabilisticConstruction.Resampling



-- Prove2me | Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryTimes
-- name    : QEC_Coding_ProbabilisticConstruction_Resampling_HistoryTimes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T19:16:53.603921+00:00
-- url     : https://prove2.me/theorems/d45927db-c17b-4b92-9cfa-66dc8b9b2868
-- title:
--   History Times
-- statement:
--   Definitions and structural lemmas for History Times, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/HistoryTimes.lean

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
set_option autoImplicit false
namespace QEC.Coding.ProbabilisticConstruction.Resampling
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]
noncomputable def timedHistoryWitness (root : I) : ℕ → List I → Finset (List I × ℕ)
  | offset, [] => {([], offset)}
  | offset, j :: rest =>
      let W := timedHistoryWitness root (offset + 1) rest
      let P := W.image Prod.fst
      if h : (attachmentCandidates G root j P).Nonempty then
        insert (attachmentParent G root j P h ++ [j], offset) W
      else W
def historyLabel (root : I) (L : List I) (n : ℕ) : I := L[n]?.getD root
section VariableSupports
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (vars : I → Finset V)
end VariableSupports
end QEC.Coding.ProbabilisticConstruction.Resampling



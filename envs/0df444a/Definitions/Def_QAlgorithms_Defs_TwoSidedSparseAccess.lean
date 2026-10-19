-- Prove2me | Definitions.Def_QAlgorithms_Defs_TwoSidedSparseAccess
-- name    : QAlgorithms_Defs_TwoSidedSparseAccess
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:39:50.581965+00:00
-- url     : https://prove2.me/theorems/159c8323-a7f6-47ec-92ff-268c3ea2d0b9
-- title:
--   TwoSidedSparseAccess
-- statement:
--   TwoSidedSparseAccess
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\TwoSidedSparseAccess.lean

import Definitions.Def_QAlgorithms_Defs_LinearSystemAccess
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.LinearSystemAccess

/-- QAlgorithms.LinearSystemAccess.IsTwoSidedSparseAccess: arxiv-2609.35660v1 PDF p.1, arxiv-2609.35660v1 PDF p.5. Source domains are explicit below. -/
def IsTwoSidedSparseAccess {N b : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (d : ℕ)
    (decode : Qubits b → ℂ)
    (Orow OadjRow : Matrix (Qubits (Nat.clog 2 N+Nat.clog 2 N))
      (Qubits (Nat.clog 2 N+Nat.clog 2 N)) ℂ)
    (Ovalue OadjValue : Matrix (Qubits (Nat.clog 2 N+Nat.clog 2 N+b))
      (Qubits (Nat.clog 2 N+Nat.clog 2 N+b)) ℂ) : Prop :=
  0 < N ∧ 1 ≤ d ∧ d ≤ N ∧ IsColumnOracle A.transpose d Orow ∧
    IsEntryOracle A decode Ovalue ∧ IsColumnOracle A.conjTranspose.transpose d OadjRow ∧
    IsEntryOracle A.conjTranspose decode OadjValue

example {N b : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (decode : Qubits b → ℂ)
    (Orow OadjRow : Matrix (Qubits (Nat.clog 2 N+Nat.clog 2 N))
      (Qubits (Nat.clog 2 N+Nat.clog 2 N)) ℂ)
    (Ovalue OadjValue : Matrix (Qubits (Nat.clog 2 N+Nat.clog 2 N+b))
      (Qubits (Nat.clog 2 N+Nat.clog 2 N+b)) ℂ) :
    ¬ IsTwoSidedSparseAccess A 0 decode Orow OadjRow Ovalue OadjValue := by
  intro h; have hp := h.2.1; norm_num at hp

end QAlgorithms.LinearSystemAccess



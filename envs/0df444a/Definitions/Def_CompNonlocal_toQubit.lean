-- Prove2me | Definitions.Def_CompNonlocal_toQubit
-- name    : CompNonlocal_toQubit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:38:58.155983+00:00
-- url     : https://prove2.me/theorems/8eddf13f-b3cc-45d6-aaed-7b7ac2a2e470
-- title:
--   One-wire matrices read on a qubit
-- statement:
--   Circuits index the basis states of $k$ wires by bit vectors $\{0,1\}^k$, while single-qubit algebra uses the basis $\{|0\rangle,|1\rangle\}$. This map identifies a matrix on the basis of one wire with a $2\times2$ qubit matrix, by the value of the single wire. It carries no mathematical content beyond this identification.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), §4.1, p.18 (qubit basis)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- A one-qubit operator on the one-wire basis `Bits 1 = Fin 1 → Bool`, read as a matrix on `Bool`.
Circuits (`QAlgorithms.Complexity`) index basis states of `k` wires by `Bits k`, while the qubit
algebra of Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), §4.1, p.18 indexes one qubit by `Bool` (`false = |0⟩`). This is the
canonical identification `Bits 1 ≃ Bool` (the value of the single wire). -/
def toQubit (M : Matrix (Bits 1) (Bits 1) ℂ) : Matrix Bool Bool ℂ :=
  Matrix.reindex (Equiv.funUnique (Fin 1) Bool) (Equiv.funUnique (Fin 1) Bool) M

end CompNonlocal



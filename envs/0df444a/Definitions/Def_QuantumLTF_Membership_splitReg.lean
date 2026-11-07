-- Prove2me | Definitions.Def_QuantumLTF_Membership_splitReg
-- name    : QuantumLTF_Membership_splitReg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:32:09.515103+00:00
-- url     : https://prove2.me/theorems/47259f91-57f2-4c65-a3c6-92dbae9cd366
-- title:
--   The $n$ sub-registers of a register of $n\ell$ wires
-- statement:
--   A register of $n\ell$ wires is split into $n$ sub-registers of $\ell$ wires each: sub-register $i$ occupies the wires $i\ell,\dots,i\ell+\ell-1$. This fixes the wire layout used by the oracle's address register.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, §3.1.2, p. 23 (PDF p. 24), "n registers"

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace QuantumLTF.Membership

open QAlgorithms

/-- **The `n` sub-registers of a register of `n * ℓ` wires.** Layout used by `addrOf`, `flatReg` and
the height oracle: sub-register `i` occupies wires `i * ℓ, …, i * ℓ + ℓ − 1` (Mathlib's
`finProdFinEquiv`), each read most significant bit first. A notational device for
Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, §3.1.2, p. 23 (PDF p. 24): "n registers". -/
def splitReg (n ℓ : ℕ) (y : Qubits (n * ℓ)) (i : Fin n) : Qubits ℓ :=
  fun j => y (finProdFinEquiv (i, j))

end QuantumLTF.Membership



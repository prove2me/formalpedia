-- Prove2me | Definitions.Def_QuantumLTF_Membership_flatReg
-- name    : QuantumLTF_Membership_flatReg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:32:06.430009+00:00
-- url     : https://prove2.me/theorems/efa070d8-94d6-40fd-bd4a-74b33cb9e996
-- title:
--   $n$ registers of $b$ wires joined into one register
-- statement:
--   The inverse of the split: $n$ bit strings of length $b$ are written on one register of $nb$ wires, the $i$-th on wires $ib,\dots,ib+b-1$. This fixes the wire layout of the grid register $|x\rangle$, $x\in G_b^n$.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, §3.1.3, p. 28 (PDF p. 29), "n registers of b qubits each"

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace QuantumLTF.Membership

open QAlgorithms

/-- **`n` registers of `b` wires joined into one of `n * b` wires**: the inverse of `splitReg`
(sub-register `i` on wires `i * b, …, i * b + b − 1`). A notational device for
Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, §3.1.3, p. 28 (PDF p. 29): "n registers of b qubits each". -/
def flatReg (n b : ℕ) (x : Fin n → Qubits b) : Qubits (n * b) :=
  fun k => x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

end QuantumLTF.Membership



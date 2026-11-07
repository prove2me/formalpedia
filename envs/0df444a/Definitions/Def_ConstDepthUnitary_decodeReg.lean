-- Prove2me | Definitions.Def_ConstDepthUnitary_decodeReg
-- name    : ConstDepthUnitary_decodeReg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:43:50.278346+00:00
-- url     : https://prove2.me/theorems/1938eb74-35cb-41ba-b07f-fafbc848b3a8
-- title:
--   Reading the $N$ bit registers as a grid point
-- statement:
--   For $N$ registers $V_j$ of $k$ qubits each, the value $v\in[2^k]^N$ with $v_j$ the integer held by $V_j$, most significant bit first. It carries the operators on $[K]^N$, $K=2^k$, to operators on the qubits.
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §6.2, Algorithm 4, p.38

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace ConstDepthUnitary

/-- The value `v ∈ [2^k]^N` held by the `N` registers `V_j = {j} × Fin k`, each big-endian
(`QAlgorithms.bitsEquivFin`).

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §6.2, Algorithm 4, p.38 ("Input: N registers V_0, …, V_{N−1}, each on k = log K qubits"). -/
def decodeReg (N k : ℕ) (y : Fin N × Fin k → Bool) : Fin N → Fin (2 ^ k) :=
  fun j => QAlgorithms.bitsEquivFin k fun b => y (j, b)

end ConstDepthUnitary



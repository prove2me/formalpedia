-- Prove2me | Definitions.Def_CollectiveDFS_partialS
-- name    : CollectiveDFS_partialS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:02:20.977387+00:00
-- url     : https://prove2.me/theorems/495c13e9-d7d6-40d5-97d5-b129d1879b5f
-- title:
--   Partial collective operator $S^k_\alpha$
-- statement:
--   For $0\le k\le n$ and $\alpha\in\{x,y,z\}$, the **partial collective operator** of (7.7) is
--   $$S^k_\alpha=\sum_{i=1}^{k}\sigma^i_\alpha,$$
--   the sum of $\sigma_\alpha$ over the first $k$ qubits. At $k=n$ it is the collective operator $S_\alpha=\sum_{j=1}^n\sigma^j_\alpha$ of (5.1), through which strong collective decoherence couples the qubits to the bath.
--
--   The spin operators of (7.10) are $s^k_\alpha=\tfrac12 S^k_\alpha$.
--
--   **Formalization Note** Wires are 0-based (wire $j$ is the paper's qubit $j+1$), and the computational basis is indexed by `Bool`, `false` being $|0\rangle$, with $\sigma_z|0\rangle=|0\rangle$ as in (5.2). For $k\ge n$ the sum runs over all wires.
-- source:
--   Kempe, Bacon, Lidar & Whaley, Theory of Decoherence-Free Fault-Tolerant Universal Quantum Computation, arXiv:quant-ph/0004064v2, eq. (7.7), p.23; eq. (5.1), p.12

import Mathlib
import Definitions.Def_CollectiveDFS_pauli
import Definitions.Def_CollectiveDFS_onWire

open QAlgorithms

namespace CollectiveDFS

/-- The partial collective operator `S^k_α = Σ_{i=1}^k σ_α^i` of (7.7) on an `n`-qubit
register (Kempe, Bacon, Lidar & Whaley, arXiv:quant-ph/0004064v2, eq. (7.7), p.23, PDF p.23). At `k = n` it is the collective operator
`S_α = Σ_{j=1}^n σ_α^j` of (5.1), p.12.

**Formalization Note** Wires are 0-based, so the paper's qubits `1, …, k` are the wires `i` with
`i < k`. For `k ≥ n` the sum runs over all wires. `α : Fin 3` with `0, 1, 2 = x, y, z`. This is
the unnormalized `S`; the spin operator of (7.10) is `s^k_α = ½ S^k_α`. -/
def partialS (n k : ℕ) (α : Fin 3) : Matrix (Qubits n) (Qubits n) ℂ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), onWire i (pauli α)

end CollectiveDFS



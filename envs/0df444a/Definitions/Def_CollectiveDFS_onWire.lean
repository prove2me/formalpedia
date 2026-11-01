-- Prove2me | Definitions.Def_CollectiveDFS_onWire
-- name    : CollectiveDFS_onWire
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:01:19.803982+00:00
-- url     : https://prove2.me/theorems/aacb7b1c-456c-4205-bab8-e9cb1dc8a936
-- title:
--   One-qubit operator $A$ on wire $j$
-- statement:
--   For a one-qubit operator $A$ and a wire $j$ of an $n$-qubit register, $A^{j}$ denotes the operator acting as $A$ on qubit $j$ and as the identity on all other qubits. In the computational basis its entry between bit strings $x,y$ is $A_{x_j y_j}$ if $x$ and $y$ agree off wire $j$, and $0$ otherwise. With $A=\sigma_\alpha$ this is the operator $\sigma^j_\alpha$ of (5.1).
--
--   **Formalization Note** Wires are 0-based (wire $j$ is the paper's qubit $j+1$), and the computational basis is indexed by `Bool`, `false` being $|0\rangle$, with $\sigma_z|0\rangle=|0\rangle$ as in (5.2).
-- source:
--   Kempe, Bacon, Lidar & Whaley, Theory of Decoherence-Free Fault-Tolerant Universal Quantum Computation, arXiv:quant-ph/0004064v2, §V, eq. (5.1), p.12

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

open QAlgorithms

namespace CollectiveDFS

/-- A one-qubit operator `A` acting on wire `j` of an `n`-qubit register and as the identity on
all other wires: the operator `σ_α^j` of (5.1) when `A = σ_α` (Kempe, Bacon, Lidar & Whaley, arXiv:quant-ph/0004064v2, §V, eq. (5.1), p.12,
PDF p.12). Its matrix entry between basis strings `x, y` is `A (x j) (y j)` when `x` and `y`
agree off wire `j`, and `0` otherwise.

**Formalization Note** Wires are 0-based: wire `j` is the paper's qubit `j + 1`. -/
def onWire {n : ℕ} (j : Fin n) (A : Matrix Bool Bool ℂ) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun x y => if ∀ k, k ≠ j → x k = y k then A (x j) (y j) else 0

end CollectiveDFS



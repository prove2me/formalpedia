-- Prove2me | Definitions.Def_CollectiveDFS_exchange
-- name    : CollectiveDFS_exchange
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:01:17.763019+00:00
-- url     : https://prove2.me/theorems/91fa0b20-9737-4b15-8a35-6d6d553397aa
-- title:
--   Exchange operator $E_{ab}$
-- statement:
--   The **exchange operator** $E_{ab}$ of two qubits $a,b$ of an $n$-qubit register swaps their states:
--   $$E_{ab}\,|k\rangle_a|l\rangle_b=|l\rangle_a|k\rangle_b,$$
--   acting as the identity on the other qubits. It is the permutation matrix that sends a basis string $y$ to the string with the entries at $a$ and $b$ exchanged.
--
--   Exchange is the only two-qubit Hermitian interaction that commutes with the collective spin, and the paper's universality theorem uses it as the only resource.
--
--   **Formalization Note** Wires are 0-based (wire $j$ is the paper's qubit $j+1$), and the computational basis is indexed by `Bool`, `false` being $|0\rangle$, with $\sigma_z|0\rangle=|0\rangle$ as in (5.2). The operator is defined as a permutation, not through its Pauli expansion (7.22), which is a separate theorem. For $a=b$ it is the identity; all statements use $a\neq b$.
-- source:
--   Kempe, Bacon, Lidar & Whaley, Theory of Decoherence-Free Fault-Tolerant Universal Quantum Computation, arXiv:quant-ph/0004064v2, §VII.B, p.24

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

open QAlgorithms

namespace CollectiveDFS

/-- The exchange operator `E_ab` of wires `a` and `b`: "`E_ij|k⟩_i|l⟩_j = |l⟩_i|k⟩_j`"
(Kempe, Bacon, Lidar & Whaley, arXiv:quant-ph/0004064v2, §VII.B, p.24, PDF p.24). It is the permutation matrix sending the basis string `y` to
`y ∘ swap a b`.

**Formalization Note** Wires are 0-based (wire `a` is the paper's qubit `a + 1`). The operator
is defined by the permutation, not by the Pauli expansion (7.22), which is a theorem
(`CollectiveDFS.exchange_pauli`). For `a = b` it is the identity; the paper uses only `a ≠ b`. -/
def exchange {n : ℕ} (a b : Fin n) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun x y => if x = y ∘ Equiv.swap a b then 1 else 0

end CollectiveDFS



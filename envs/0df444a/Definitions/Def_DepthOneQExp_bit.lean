-- Prove2me | Definitions.Def_DepthOneQExp_bit
-- name    : DepthOneQExp_bit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:44:02.485092+00:00
-- url     : https://prove2.me/theorems/3d9075b5-7656-4f8b-83a4-b33d6188b3e4
-- title:
--   Bit $x_j$ of a basis string, qubit index taken periodically
-- statement:
--   For an $n$-qubit computational-basis string $x\in\{0,1\}^n$ and a qubit index $j$, $\mathrm{bit}(x,j)$ is the bit of $x$ on qubit $j \bmod n$. The paper takes qubit indices "with periodic condition" (Theorem 2.2), so a gate written on qubit $3i+4$ of a $3s$-qubit register acts on qubit $(3i+4) \bmod 3s$.
--
--   **Formalization Note** Qubits are 0-based: the paper's qubit $p\ge 1$ is index $(p-1)\bmod n$, so the paper's qubit 1 is index $0$. For $n=0$ the value is $0$ (never used).
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Theorem 2.2, p.7 ("the indices are taken with periodic condition")

import Mathlib
import Definitions.Def_MITMSynthesis_Gate

namespace DepthOneQExp

/-- The bit of a computational-basis string `x ∈ {0,1}ⁿ` on qubit `j`, with the qubit index taken
**periodically** (Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1 expanders on the unitary
group and applications*, arXiv:2609.01605, held version sha256 3c3f8513…aebfd87, Theorem 2.2,
pp.6–7: "the indices are taken with periodic condition").

**Formalization Note** Qubits are 0-based: the paper's qubit `p` (`1 ≤ p`) is index `(p − 1) mod n`
here, so the paper's qubit 1 is index `0`. For `n = 0` there is no qubit and the value is `0`
(never used: every register in the mission has `n ≥ 1` qubits). -/
def bit {n : ℕ} (x : MITMSynthesis.Q n) (j : ℕ) : Fin 2 :=
  if h : j % n < n then x ⟨j % n, h⟩ else 0

end DepthOneQExp



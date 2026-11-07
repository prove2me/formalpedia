-- Prove2me | Definitions.Def_QuantumHMMR_AdaptiveAlg
-- name    : QuantumHMMR_AdaptiveAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:34:34.936173+00:00
-- url     : https://prove2.me/theorems/128ba1f3-205f-4c0b-8778-2201213d075c
-- title:
--   Adaptive $t$-query oracle algorithm
-- statement:
--   A **$t$-query quantum oracle algorithm** with access to an $n$-qubit unitary $U$ consists of a number $m \in \mathbb N$ of ancilla qubits and unitaries $A_0, \dots, A_t$ on $n + m$ qubits (an $n$-qubit register $A$ and an $m$-qubit ancilla register $B$). It implements
--   $$
--   A_t \cdot U \cdot A_{t-1} \cdot U \cdots A_1 \cdot U \cdot A_0, \tag{4}
--   $$
--   where each $U$ acts on register $A$. The algorithm is adaptive: later unitaries act on the outputs of earlier queries.
--
--   **Formalization Note** Register $A$ is wires $0, \dots, n-1$, register $B$ the remaining wires. $m = 0$ is allowed.
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), Section 3, Eq. (4), p.10

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

open QAlgorithms

namespace QuantumHMMR

/-- A `t`-query quantum oracle algorithm with access to an `n`-qubit unitary oracle (Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), §3,
Eq. (4), p.10): a number `anc = m` of ancilla qubits and `t + 1` unitaries `A_0, …, A_t` acting on
the `n + m` qubits of the registers `AB`, interleaved with `t` oracle calls as
`A_t · U · A_{t-1} ⋯ A_1 · U · A_0`.

**Formalization Note** `A k` is `A_k`; `A 0` acts first. The oracle register `A` is wires
`0, …, n - 1` and the ancilla register `B` is wires `n, …, n + anc - 1`. The ancilla count is any
natural number ("for `m ∈ ℕ`"), including `0`. -/
structure AdaptiveAlg (n t : ℕ) where
  /-- The number `m` of ancilla qubits (register `B`). -/
  anc : ℕ
  /-- The interleaved unitaries `A_0, …, A_t` on `n + anc` qubits. -/
  A : Fin (t + 1) → Matrix.unitaryGroup (Qubits (n + anc)) ℂ

end QuantumHMMR



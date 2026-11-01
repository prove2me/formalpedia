-- Prove2me | Definitions.Def_CollectiveDFS_LegalJ
-- name    : CollectiveDFS_LegalJ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:01:13.195208+00:00
-- url     : https://prove2.me/theorems/7db9752d-c754-467b-86ca-a62cc580814f
-- title:
--   Legal total spin $J$ for $n$ qubits
-- statement:
--   A total spin $J$ is **legal** for $n$ qubits when $J\in\{\tfrac n2,\tfrac n2-1,\dots\}$ down to $0$ or $\tfrac12$: $2J$ is a natural number with $2J\le n$ and $2J\equiv n\pmod 2$. These are the values of $J$ in the sums (7.1)–(7.2).
--
--   **Formalization Note** Spin and magnetic labels are doubled: a natural number $j_2=2J$ and an integer $m_2=2m$, so half-integers are exact.
-- source:
--   Kempe, Bacon, Lidar & Whaley, Theory of Decoherence-Free Fault-Tolerant Universal Quantum Computation, arXiv:quant-ph/0004064v2, eqs. (7.1)–(7.2), p.20

import Mathlib

namespace CollectiveDFS

/-- `J = j2/2` is a total spin occurring for `n` qubits: `J ∈ {n/2, n/2 − 1, …}` down to `0` or
`1/2` (Kempe, Bacon, Lidar & Whaley, arXiv:quant-ph/0004064v2, eqs. (7.1)–(7.2), p.20, PDF p.20: "`J = 0 (1/2)` … `n/2`").

**Formalization Note** Doubled label: `2J = j2 ≤ n` and `2J ≡ n (mod 2)`. -/
def LegalJ (n j2 : ℕ) : Prop :=
  j2 ≤ n ∧ j2 % 2 = n % 2

end CollectiveDFS



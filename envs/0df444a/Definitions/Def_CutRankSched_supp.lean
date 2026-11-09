-- Prove2me | Definitions.Def_CutRankSched_supp
-- name    : CutRankSched_supp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:30:31.266938+00:00
-- url     : https://prove2.me/theorems/9e0d514d-4b58-44d8-9ab4-4aa1fdc39480
-- title:
--   Support $\operatorname{supp}(p)$ of a binary Pauli vector
-- statement:
--   The **support** of a binary Pauli vector $p = (x, z)$ on $m$ qubits is the set of qubits on which it acts nontrivially,
--   $$
--   \operatorname{supp}(p) = \{\, q \in Q : x_q \ne 0 \text{ or } z_q \ne 0 \,\}.
--   $$
--   It is nonempty exactly when $p \ne 0$.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Section 3.1, p.4

import Mathlib
import Definitions.Def_CutRankSched_Pauli

set_option autoImplicit false

namespace CutRankSched

/-- The support `supp(p)` of a binary Pauli vector `p = (x, z)`: the qubits `q` with
`x_q ≠ 0` or `z_q ≠ 0` (Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §3.1, p.4). -/
def supp {m : ℕ} (p : Pauli m) : Finset (Fin m) :=
  Finset.univ.filter fun q => p.1 q ≠ 0 ∨ p.2 q ≠ 0

end CutRankSched



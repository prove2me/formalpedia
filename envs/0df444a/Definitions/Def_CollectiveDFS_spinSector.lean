-- Prove2me | Definitions.Def_CollectiveDFS_spinSector
-- name    : CollectiveDFS_spinSector
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:04:50.691997+00:00
-- url     : https://prove2.me/theorems/f2aff2cb-493c-4f5d-8651-5964430d328a
-- title:
--   Spin-$J$ sector $W_J$
-- statement:
--   The **spin-$J$ sector** $W_J$ of $n$ qubits is the $J(J+1)$-eigenspace of the total Casimir $(s^n)^2$. In the decomposition (7.2), $H_S\cong\bigoplus_J \mathbb C^{n_J}\otimes\mathbb C^{2J+1}$, it is the summand $\mathbb C^{n_J}\otimes\mathbb C^{2J+1}$: the collective operators act on the second factor and the exchanges on the first.
--
--   **Formalization Note** Spin and magnetic labels are doubled: a natural number $j_2=2J$ and an integer $m_2=2m$, so half-integers are exact. For an illegal label the sector is zero.
-- source:
--   Kempe, Bacon, Lidar & Whaley, Theory of Decoherence-Free Fault-Tolerant Universal Quantum Computation, arXiv:quant-ph/0004064v2, eqs. (7.1)–(7.2), p.20; eq. (7.12), p.23

import Mathlib
import Definitions.Def_CollectiveDFS_casimirEigenspace

open QAlgorithms

namespace CollectiveDFS

/-- The total-spin-`J` sector `W_J` of `n` qubits, `J = j2/2`: the `J(J+1)`-eigenspace of the
total Casimir `(s^n)²`. In the decomposition (7.2) it is the summand `C^{n_J} ⊗ C^{2J+1}`
(Kempe, Bacon, Lidar & Whaley, arXiv:quant-ph/0004064v2, eqs. (7.1)–(7.2), p.20, and (7.12), p.23, PDF pp.20, 23).

**Formalization Note** Doubled label `j2 = 2J`. For an illegal `j2` (wrong parity or `j2 > n`) the
sector is `⊥`. -/
noncomputable def spinSector (n j2 : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Qubits n)) :=
  casimirEigenspace n n j2

end CollectiveDFS



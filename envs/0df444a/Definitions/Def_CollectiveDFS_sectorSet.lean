-- Prove2me | Definitions.Def_CollectiveDFS_sectorSet
-- name    : CollectiveDFS_sectorSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:05:40.682617+00:00
-- url     : https://prove2.me/theorems/1ec2de8a-9623-4f5e-8ea8-84a12564bd02
-- title:
--   The set $H^n_J$ of Theorem 5
-- statement:
--   For $n$ qubits and a spin $J$, $H^n_J$ is the set of Hamiltonians $X$ such that
--   1. $X$ is Hermitian,
--   2. $X$ is obtained from exchange: $iX\in\mathfrak g_n$,
--   3. $X$ vanishes on the orthogonal complement of the spin-$J$ sector $W_J$, i.e. it has "zeroes in the matrix representation corresponding to [its] action on the other DFSs", and
--   4. $\operatorname{tr}X=0$.
--
--   It is the largest set with the properties Theorem 5 asks of the sets $H^n_J$.
--
--   **Formalization Note** Spin and magnetic labels are doubled: a natural number $j_2=2J$ and an integer $m_2=2m$, so half-integers are exact. The trace is over the whole space. It is needed: at $n=3$, $E_{12}+E_{13}+E_{23}$ vanishes off $J=3/2$ but acts on the one-dimensional $\mathrm{DFS}_3(3/2)$ as the scalar $3$.
-- source:
--   Kempe, Bacon, Lidar & Whaley, Theory of Decoherence-Free Fault-Tolerant Universal Quantum Computation, arXiv:quant-ph/0004064v2, Theorem 5, p.26

import Mathlib
import Definitions.Def_CollectiveDFS_exchangeLie
import Definitions.Def_CollectiveDFS_spinSector

open QAlgorithms

namespace CollectiveDFS

/-- The set `H^n_J` of Theorem 5 at full size: the Hermitian `X` obtained from exchange
(`i X ∈ exchangeLie n`) that vanish on the orthogonal complement of the spin-`J` sector, i.e.
"with zeroes in the matrix representation corresponding to their action on the other DFSs", and
are traceless (Kempe, Bacon, Lidar & Whaley, arXiv:quant-ph/0004064v2, Theorem 5, p.26, PDF p.26).

**Formalization Note** Doubled label `j2 = 2J`. The trace is over the whole space. It is needed:
at `n = 3`, `E₁₂ + E₁₃ + E₂₃` vanishes off `J = 3/2` but acts on the one-dimensional
`DFS_3(3/2)` as the nonzero scalar `3`. -/
def sectorSet (n j2 : ℕ) : Set (Matrix (Qubits n) (Qubits n) ℂ) :=
  {X | X.IsHermitian ∧ Complex.I • X ∈ exchangeLie n ∧
    (∀ ψ ∈ (spinSector n j2)ᗮ, Matrix.toEuclideanLin X ψ = 0) ∧ X.trace = 0}

end CollectiveDFS



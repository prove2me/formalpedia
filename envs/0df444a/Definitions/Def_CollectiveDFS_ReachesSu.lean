-- Prove2me | Definitions.Def_CollectiveDFS_ReachesSu
-- name    : CollectiveDFS_ReachesSu
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:06:52.020011+00:00
-- url     : https://prove2.me/theorems/48d4f535-a93f-4e83-83f9-939b97250db0
-- title:
--   Exchange acts as $\mathfrak{su}$ on $\mathrm{DFS}_n(J)$, independently
-- statement:
--   Exchange **acts as $\mathfrak{su}$ independently** on $D=\mathrm{DFS}_n(J)$ at magnetic number $m$ when every element $A$ of $\mathfrak{su}(D)$ (a traceless Hermitian operator on $D$, extended by zero) agrees on $D$ with some $X\in H^n_J$, i.e. with a Hamiltonian obtained from exchange that annihilates every sector other than $W_J$.
--
--   This is the paper's "Hamiltonians which annihilate all of the DFSs except a desired one on which they act as $\mathfrak{su}(n_J)$" (p.26).
--
--   **Formalization Note** Spin and magnetic labels are doubled: a natural number $j_2=2J$ and an integer $m_2=2m$, so half-integers are exact.
-- source:
--   Kempe, Bacon, Lidar & Whaley, Theory of Decoherence-Free Fault-Tolerant Universal Quantum Computation, arXiv:quant-ph/0004064v2, §VII.D, p.26

import Mathlib
import Definitions.Def_CollectiveDFS_IsSuOn
import Definitions.Def_CollectiveDFS_sectorSet
import Definitions.Def_CollectiveDFS_dfs

open QAlgorithms

namespace CollectiveDFS

/-- Exchange acts as all of `su` on `DFS_n(J)` at magnetic number `m`, independently: every
traceless Hermitian operator `A` on `D = dfs n j2 m2` (extended by zero) agrees on `D` with
some `X ∈ H^n_J` (`sectorSet n j2`), a Hamiltonian from exchange that vanishes off the spin-`J`
sector. This is "perform su(n_J) on DFS_n(J) independently" in the induction hypothesis
(Kempe, Bacon, Lidar & Whaley, arXiv:quant-ph/0004064v2, §VII.D, p.26, PDF p.26: "Hamiltonians which annihilate all of the DFSs except a desired one
on which they act as su(n_J)").

**Formalization Note** Doubled labels `j2 = 2J`, `m2 = 2m`. -/
def ReachesSu (n j2 : ℕ) (m2 : ℤ) : Prop :=
  ∀ A : Matrix (Qubits n) (Qubits n) ℂ, IsSuOn (dfs n j2 m2) A →
    ∃ X ∈ sectorSet n j2, ∀ ψ ∈ dfs n j2 m2,
      Matrix.toEuclideanLin X ψ = Matrix.toEuclideanLin A ψ

end CollectiveDFS



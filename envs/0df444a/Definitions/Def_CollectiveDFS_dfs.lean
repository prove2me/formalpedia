-- Prove2me | Definitions.Def_CollectiveDFS_dfs
-- name    : CollectiveDFS_dfs
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:05:53.049831+00:00
-- url     : https://prove2.me/theorems/0b7e17ed-31e0-451d-9ba4-7d318c5144af
-- title:
--   The DFS $\mathrm{DFS}_n(J)$ at magnetic number $m$
-- statement:
--   The **decoherence-free subsystem** $\mathrm{DFS}_n(J)$ at magnetic number $m$ is the subspace
--   $$D_{J,m}=W_J\cap\{\psi:\ s_z\psi=m\psi\}$$
--   of the $n$-qubit space: "a DFS is defined by fixing $J$ and $\mu$" (p.20), with $\mu=m_J$ (p.23). It is a copy of $\mathbb C^{n_J}$ inside the physical space, and the encoded information lives in it.
--
--   **Formalization Note** Spin and magnetic labels are doubled: a natural number $j_2=2J$ and an integer $m_2=2m$, so half-integers are exact. The DFS is a subspace of the physical space, not the abstract multiplicity space $\mathbb C^{n_J}$.
-- source:
--   Kempe, Bacon, Lidar & Whaley, Theory of Decoherence-Free Fault-Tolerant Universal Quantum Computation, arXiv:quant-ph/0004064v2, §VII, p.20; p.23

import Mathlib
import Definitions.Def_CollectiveDFS_spinSector
import Definitions.Def_CollectiveDFS_szEigenspace

open QAlgorithms

namespace CollectiveDFS

/-- The strong collective decoherence DFS `DFS_n(J)` at magnetic number `m`: the subspace of the
`n`-qubit space where `(s^n)² = J(J+1)` and `s_z = m`. "A DFS is defined by fixing J and µ"
(Kempe, Bacon, Lidar & Whaley, arXiv:quant-ph/0004064v2, §VII, p.20, PDF p.20), with `µ = m_J` (p.23). It is a copy of `C^{n_J}` inside the physical
space, not an abstract multiplicity space.

**Formalization Note** Doubled labels `j2 = 2J`, `m2 = 2m`. -/
noncomputable def dfs (n j2 : ℕ) (m2 : ℤ) : Submodule ℂ (EuclideanSpace ℂ (Qubits n)) :=
  spinSector n j2 ⊓ szEigenspace n m2

end CollectiveDFS



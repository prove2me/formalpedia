-- Prove2me | Definitions.Def_CollectiveDFS_pathSpace
-- name    : CollectiveDFS_pathSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:04:35.601966+00:00
-- url     : https://prove2.me/theorems/55830c4a-a062-4b2c-9ab5-bc3be4dc159f
-- title:
--   Joint eigenspace of a path
-- statement:
--   For a path $(J_1,\dots,J_n)$ and a magnetic number $m$, this is the joint eigenspace
--   $$\{\psi:\ (s^k)^2\psi=J_k(J_k+1)\psi\ \text{for } k=1,\dots,n,\ \ s_z\psi=m\psi\}.$$
--   For a legal $m$ it is the line spanned by the basis vector $|J_1,J_2,\dots,J_{n-1},J;m_J\rangle$ of (7.11)–(7.12).
--
--   **Formalization Note** Labels doubled, positions 0-based ($p(k)$ labels $(s^{k+1})^2$). The space is defined without a phase convention; the paper's basis vector is a unit vector of it, fixed up to a phase.
-- source:
--   Kempe, Bacon, Lidar & Whaley, Theory of Decoherence-Free Fault-Tolerant Universal Quantum Computation, arXiv:quant-ph/0004064v2, eqs. (7.11)–(7.12), p.23

import Mathlib
import Definitions.Def_CollectiveDFS_casimirEigenspace
import Definitions.Def_CollectiveDFS_szEigenspace

open QAlgorithms

namespace CollectiveDFS

/-- The joint eigenspace of the commuting partial Casimirs labelled by a path, at magnetic number
`m`: the vectors `ψ` with `(s^k)² ψ = J_k(J_k+1) ψ` for every `k = 1, …, n` and `s_z ψ = m ψ`.
For a path and a legal `m` it is the line spanned by the basis vector
`|J_1, J_2, …, J_{n−1}, J; m_J⟩` of (7.11)–(7.12) (Kempe, Bacon, Lidar & Whaley, arXiv:quant-ph/0004064v2, eqs. (7.11)–(7.12), p.23, PDF p.23).

**Formalization Note** Doubled labels, 0-based positions: `p k = 2 J_{k+1}`, so `p k` labels the
eigenvalue of `(s^{k+1})²`. The space is defined without phase conventions; the paper's basis
vector is a unit vector in it, fixed up to a phase. -/
noncomputable def pathSpace {n : ℕ} (p : Fin n → ℕ) (m2 : ℤ) :
    Submodule ℂ (EuclideanSpace ℂ (Qubits n)) :=
  (⨅ k : Fin n, casimirEigenspace n ((k : ℕ) + 1) (p k)) ⊓ szEigenspace n m2

end CollectiveDFS



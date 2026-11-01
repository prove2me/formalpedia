-- Prove2me | Definitions.Def_CollectiveDFS_casimirEigenspace
-- name    : CollectiveDFS_casimirEigenspace
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:03:45.414001+00:00
-- url     : https://prove2.me/theorems/e00ad9db-9685-4104-b154-90f8aa14f172
-- title:
--   Eigenspace of $(s^k)^2$ for $J_k(J_k+1)$
-- statement:
--   For $0\le k\le n$ and a spin $J_k\in\{0,\tfrac12,1,\dots\}$, this is the subspace of the $n$-qubit space
--   $$\{\psi:\ (s^k)^2\psi=J_k(J_k+1)\,\psi\},$$
--   the eigenspace of the partial Casimir appearing in (7.12).
--
--   **Formalization Note** Spin and magnetic labels are doubled: a natural number $j_2=2J$ and an integer $m_2=2m$, so half-integers are exact. Requiring $j_2\in\mathbb N$ excludes the spurious label $-J-1$, which has the same value of $J(J+1)$. Vectors live in $\mathbb C^{2^n}$ with its standard inner product.
-- source:
--   Kempe, Bacon, Lidar & Whaley, Theory of Decoherence-Free Fault-Tolerant Universal Quantum Computation, arXiv:quant-ph/0004064v2, eq. (7.12), p.23

import Mathlib
import Definitions.Def_CollectiveDFS_partialCasimir

open QAlgorithms

namespace CollectiveDFS

/-- The eigenspace of the partial Casimir `(s^k)²` for the eigenvalue `J_k(J_k+1)`, with
`J_k = j2 / 2` (Kempe, Bacon, Lidar & Whaley, arXiv:quant-ph/0004064v2, eq. (7.12), p.23, PDF p.23): the vectors `ψ` of the `n`-qubit space with
`(s^k)² ψ = J_k(J_k+1) ψ`.

**Formalization Note** Spin labels are doubled: `j2 : ℕ` stands for `J_k = j2/2`, so that half-
integers are exact and `J_k ≥ 0` holds by typing (the label `J(J+1)` is symmetric under
`J ↦ −J−1`, which the natural number rules out). Vectors live in `EuclideanSpace ℂ (Qubits n)`
with the standard inner product; matrices act by `Matrix.toEuclideanLin`. -/
noncomputable def casimirEigenspace (n k j2 : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Qubits n)) :=
  LinearMap.ker (Matrix.toEuclideanLin
    (partialCasimir n k - (((j2 : ℂ) / 2) * ((j2 : ℂ) / 2 + 1)) • (1 : Matrix (Qubits n) (Qubits n) ℂ)))

end CollectiveDFS



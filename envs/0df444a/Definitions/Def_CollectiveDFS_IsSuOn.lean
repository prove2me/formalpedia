-- Prove2me | Definitions.Def_CollectiveDFS_IsSuOn
-- name    : CollectiveDFS_IsSuOn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:01:13.109266+00:00
-- url     : https://prove2.me/theorems/4890cfee-7066-4e23-ba54-997a1d87f393
-- title:
--   $A$ acts as $\mathfrak{su}(U)$ on a subspace $U$
-- statement:
--   For a subspace $U$ of $\mathbb C^\iota$, a matrix $A$ is an element of $\mathfrak{su}(U)$ extended by zero when
--   1. $A$ is Hermitian,
--   2. $A$ maps $U$ into $U$,
--   3. $A$ vanishes on the orthogonal complement $U^\perp$, and
--   4. $\operatorname{tr}A=0$.
--
--   This is what it means for a Hamiltonian to act as an element of $\mathfrak{su}$ on a subspace: the paper identifies $\mathfrak{su}(d_K)$ with the traceless Hermitian matrices on the DFS (p.11).
--
--   **Formalization Note** Stated for matrices over any finite index type acting on $\mathbb C^\iota$ with the standard inner product. Since $A$ vanishes on $U^\perp$, its trace equals the trace of its restriction to $U$.
-- source:
--   Kempe, Bacon, Lidar & Whaley, Theory of Decoherence-Free Fault-Tolerant Universal Quantum Computation, arXiv:quant-ph/0004064v2, §IV.B, p.11; Theorem 5, p.26

import Mathlib

namespace CollectiveDFS

/-- `A` is an element of `su(U)` extended by zero: `A` is Hermitian, maps the subspace `U` into
itself, vanishes on `Uᗮ`, and has trace `0`. This is the meaning of "acting as su(·)" on a
subspace, i.e. traceless Hermitian operators on it (Kempe, Bacon, Lidar & Whaley, arXiv:quant-ph/0004064v2, §IV.B, p.11, PDF p.11: "su(d_K)
(traceless matrices)"; Theorem 5, p.26).

**Formalization Note** Stated for matrices over any finite index type, acting on
`EuclideanSpace ℂ ι` by `Matrix.toEuclideanLin`. Since `A` vanishes on `Uᗮ`, `trace A` equals
the trace of `A` restricted to `U`. -/
def IsSuOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Submodule ℂ (EuclideanSpace ℂ ι)) (A : Matrix ι ι ℂ) : Prop :=
  A.IsHermitian ∧ (∀ ψ ∈ U, Matrix.toEuclideanLin A ψ ∈ U) ∧
    (∀ ψ ∈ Uᗮ, Matrix.toEuclideanLin A ψ = 0) ∧ A.trace = 0

end CollectiveDFS



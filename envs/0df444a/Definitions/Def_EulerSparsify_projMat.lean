-- Prove2me | Definitions.Def_EulerSparsify_projMat
-- name    : EulerSparsify_projMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:31:24.410565+00:00
-- url     : https://prove2.me/theorems/c43e4eea-3ae5-42ca-8859-964e51fc3f65
-- title:
--   Orthogonal projection matrix $P_S$
-- statement:
--   For a linear subspace $S$ of $\mathbb R^\iota$ (standard inner product), $P_S$ is the matrix of the orthogonal projection onto $S$: $P_S=P_S^\top=P_S^2$ and $\mathrm{im}(P_S)=S$.
--
--   **Formalization Note** Computed from Mathlib's orthogonal projection onto a subspace of the Euclidean space.
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), §3, Linear algebra, p.8 (PDF p.10)

import Mathlib

namespace EulerSparsify

/-- **Orthogonal projection matrix** `P_S` onto a subspace `S ⊆ ℝ^ι` (§3, "Linear algebra", p.8,
PDF p.10).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), p.8: "For a linear subspace S of ℝ^d, dim(S) is its dimension and P_S is the orthogonal
projection matrix onto S."

**Formalization Note.** `S` is a subspace of `EuclideanSpace ℝ ι` (standard inner product), and
`projMat S` is the matrix of Mathlib's orthogonal projection `S.starProjection`. -/
noncomputable def projMat {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Submodule ℝ (EuclideanSpace ℝ ι)) : Matrix ι ι ℝ :=
  Matrix.toEuclideanLin.symm (S.starProjection : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)

end EulerSparsify



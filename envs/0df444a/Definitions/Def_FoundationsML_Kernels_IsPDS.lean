-- Prove2me | Definitions.Def_FoundationsML_Kernels_IsPDS
-- name    : FoundationsML_Kernels_IsPDS
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T22:57:55.508855+00:00
-- url     : https://prove2.me/theorems/4612b97e-d32c-4ca1-8305-d5744d88670a
-- title:
--   Positive definite symmetric (PDS) kernel
-- statement:
--   **Definition 6.3 (Positive definite symmetric kernels), p. 108, PDF p. 125.** A kernel
--   $K : X\times X\to\mathbb R$ is positive definite symmetric (PDS) if for any
--   $\{x_1,\dots,x_m\}\subseteq X$, the matrix $\mathbf K = [K(x_i,x_j)]_{ij}\in\mathbb
--   R^{m\times m}$ is symmetric positive semidefinite (SPSD): $\mathbf K$ is symmetric and, for
--   any $c=(c_1,\dots,c_m)^\top\in\mathbb R^m$, $c^\top \mathbf K c = \sum_{i,j=1}^m c_ic_j
--   K(x_i,x_j)\ge0$.
--
--   **Formalization Note.** `IsPDS K` is `K` symmetric plus `∀ (S : Finset X) (c : X → ℝ), 0 ≤
--   ∑_{i,j∈S} c i * c j * K i j` — the book's own second (`c^T K c ≥ 0`) SPSD characterization,
--   avoiding spectral theory for a `Prop`-valued definition.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 108, Definition 6.3 (PDF p. 125)

import Mathlib

namespace FoundationsML.Kernels

/-- A kernel `K : X × X → ℝ` is positive definite symmetric (PDS) (Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, Definition 6.3, p. 108,
PDF p. 125): `K` is symmetric, and for any finite set of points `{x_1,…,x_m} ⊆ X` and any
`c_1,…,c_m ∈ ℝ`, `∑_{i,j} c_i c_j K(x_i,x_j) ≥ 0` — i.e. the kernel matrix `[K(x_i,x_j)]` is
symmetric positive semidefinite (SPSD) for every finite sample.

**Formalization Note.** Uses the book's own second SPSD characterization
(`c^T K c ≥ 0` for every `c`, Definition 6.3's displayed condition (6.2)) rather than the
non-negative-eigenvalues characterization, since it avoids spectral theory for a `Prop`-valued
definition; the book states the two are equivalent. -/
def IsPDS {X : Type*} (K : X → X → ℝ) : Prop :=
  (∀ x y : X, K x y = K y x) ∧
  ∀ (S : Finset X) (c : X → ℝ), 0 ≤ ∑ i ∈ S, ∑ j ∈ S, c i * c j * K i j

end FoundationsML.Kernels



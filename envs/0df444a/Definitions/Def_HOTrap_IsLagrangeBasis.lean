-- Prove2me | Definitions.Def_HOTrap_IsLagrangeBasis
-- name    : HOTrap_IsLagrangeBasis
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:46:00.408315+00:00
-- url     : https://prove2.me/theorems/e930541d-832c-427d-815b-8b603a2bc5a5
-- title:
--   Lagrange basis of a node set
-- statement:
--   The Lagrange basis $\ell_1,\dots,\ell_n\in P$ of nodes $z_1,\dots,z_n$ satisfies $\ell_i(z_k)=\mathbf 1\{i=k\}$.
--
--   It is the basis in which the interpolant and the stability constants are written.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, p.54

import Mathlib

namespace HOTrap

/-- **The Lagrange basis** `ℓ₁,…,ℓₙ ∈ P` of the nodes `z₁,…,zₙ`: `ℓᵢ(z_k) = 1{i=k}`. Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, p.54. -/
def IsLagrangeBasis {d : ℕ} {ι : Type*} (Q : Submodule ℝ (EuclideanSpace ℝ (Fin d) → ℝ)) (z : ι → EuclideanSpace ℝ (Fin d))
    (ℓ : ι → EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  (∀ i, ℓ i ∈ Q) ∧ (∀ i, ℓ i (z i) = 1) ∧ ∀ i k, i ≠ k → ℓ i (z k) = 0

end HOTrap


